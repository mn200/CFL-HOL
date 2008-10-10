open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
parserDefTheory yaccDefTheory parseProp1DefTheory parseProp2DefTheory
lrGrammarDefTheory

val _ = new_theory "validItemInv"


val _ = Globals.linewidth := 60;




val stkItl = Define `stkItl stl = SND (FST (HD stl))`

val initStateCsl = Define 
`initStateCsl csl = SND (LAST csl)`

val stkSymsCsl = Define 
`stkSymsCsl csl = REVERSE (MAP FST csl)`


val validItemInv = Define `
  validItemInv (ag, (stl:((symbol # item list) # ptree) list), 
	   csl) = 
!stk.IS_PREFIX (REVERSE stl) stk ==> ~NULL stk ==>
    (* (NULL stk /\ 
    (trans ag (initItems ag (rules ag), stackSyms stk)	        
     = SOME (initStateCsl ((s,itl)::csl)))) \/*)
    (trans ag (initItems ag (rules ag), stackSyms (REVERSE stk))	        
     = SOME (stkItl (REVERSE stk)))`


(* validItem holds in initial state *)
val validItemInvInit = store_thm 
("validItemInvInit",
``!m g sl st.
validItemInv (ag, [], [((NTS st), initItems ag (rules ag))])``,
SRW_TAC [] [validItemInv] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
SRW_TAC [] [stackSyms_def, trans_def, FRONT_DEF, stkSymsCsl,
	    stkItl, initStateCsl] THEN
METIS_TAC [NULL])



val isPfxTaken = store_thm
("isPfxTaken",
``!stl n stl'.(take n stl = SOME stl') ==> 
      IS_PREFIX stl stl'``,
Induct_on `n` THEN 
SRW_TAC [] []
THENL[
      Cases_on `stl` THEN
      FULL_SIMP_TAC (srw_ss()) [take_def, take1] THEN
      METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL],

      `(if (LENGTH stl >= SUC n) then SOME (take1 (SUC n) stl) 
	else NONE) = SOME stl'` by METIS_TAC [take_def] THEN
      Cases_on `LENGTH stl >= SUC n` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `stl` THEN
      FULL_SIMP_TAC (srw_ss()) [take1] THEN
      FULL_SIMP_TAC (arith_ss) [] THEN
      `LENGTH t >= n` by DECIDE_TAC THEN
      `stl'=h::take1 n t` by METIS_TAC [] THEN
      SRW_TAC [] [IS_PREFIX] THEN
      FULL_SIMP_TAC (srw_ss()) [take_def]
      ])


val isPfxRevPop = store_thm 
("isPfxRevPop",
``!l l' n.IS_PREFIX (REVERSE (pop l n)) l' ==>
  IS_PREFIX (REVERSE l) l'``,
Induct_on `n` THEN SRW_TAC [] [pop_def] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
METIS_TAC [APPEND_ASSOC, IS_PREFIX_APPEND])


val stateNotNilInv = Define
`stateNotNilInv csl = 
  !stk.IS_PREFIX (REVERSE csl) stk ==>
		 ~(itemlist stk = [])`





val isPfxPopMore = store_thm
("isPfxPopMore",
``!l n l1.IS_PREFIX l (REVERSE (pop l1 n)) ==>
  !l'.IS_PREFIX (l++l') (REVERSE (pop l1 (SUC n)))``,
Induct_on `n` THEN SRW_TAC [] [] THEN
Cases_on `l1` THEN 
FULL_SIMP_TAC (srw_ss()) [pop_def, IS_PREFIX] THEN
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [pop_def, IS_PREFIX] THEN
`IS_PREFIX l (REVERSE t'++[h'])`
by METIS_TAC [IS_PREFIX_APPEND1] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
METIS_TAC [APPEND_ASSOC])



val isPfxPopSame = store_thm
("isPfxPopSame",
``!l n l1.IS_PREFIX l (REVERSE (pop l1 n)) ==>
  !l'.IS_PREFIX (l++l') (REVERSE (pop l1 n))``,
Induct_on `n` THEN SRW_TAC [] [] THEN
Cases_on `l1` THEN 
FULL_SIMP_TAC (srw_ss()) [pop_def, IS_PREFIX] THEN
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [pop_def, IS_PREFIX] THEN
METIS_TAC [IS_PREFIX_APPEND1, IS_PREFIX_APPEND, APPEND_ASSOC])


val isPfxRevPopRefl = store_thm
("isPfxRevPopRefl",
``!l n.IS_PREFIX (REVERSE l) (REVERSE (pop l n))``,
Induct_on `n` THEN Induct_on `l` THEN 
SRW_TAC [] [pop_def, IS_PREFIX] 
THENL[
      Cases_on `l` THEN 
      FULL_SIMP_TAC (srw_ss()) [pop_def, IS_PREFIX_REFL, IS_PREFIX],
      METIS_TAC [isPfxPopSame]])



val itemlist_append = store_thm ("itemlist_append",
``!l.~(l=[]) ==> (itemlist l = itemlist (l++l'))``,
Induct_on `l` THEN SRW_TAC [] [itemlist_def])



val pop_last = store_thm
("pop_last",
``!l n.~(pop l n = []) ==>
   (LAST l = LAST (pop l n))``,
Induct_on `n` THEN SRW_TAC [] [pop_def] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
Q_TAC SUFF_TAC `~(t=[])`
THENL[

      SRW_TAC [] [] THEN
      METIS_TAC [APPEND, last_append],

      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [pop_def]
      ])


val isPfx1 = store_thm ("isPfx1",
      ``!l1 l3 e.IS_PREFIX (l1++[e]) l3 ==>
        IS_PREFIX l3 l1 ==>
        (l3=l1) \/ (l3=l1++[e])``,
	  Induct_on `l1` THEN SRW_TAC [] [IS_PREFIX] THEN
      Cases_on `l3` THEN 
      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX, IS_PREFIX_NIL])
		    

val auggrStRtcRdEof = store_thm 
("auggrStRtcRdEof",
``(auggr g st eof = SOME ag) ==>
  RTC (rderives ag) [NTS (startSym ag)] (p++[h]) ==>
  EVERY isTmnlSym (p++[h]) ==>
  (h=TS eof)``,

SRW_TAC [] [Once RTC_CASES2] 
THENL[
      Cases_on `p` THEN
      Cases_on `h` THEN 
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def],


      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [] [] THEN
      Cases_on `lhs=startSym ag` THEN
      SRW_TAC [] []
      THENL[
	    `(s1=[]) /\ (s2=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
	    SRW_TAC [] [] THEN
	    `rhs=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
	    SRW_TAC [] [] THEN
	    Cases_on `h` THEN Cases_on `p` THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
	    SRW_TAC [] [],

	    `?p.s2=p++[TS eof]` by METIS_TAC [lastEof] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [last_elem, NOT_CONS_NIL, MEM, MEM_APPEND, APPEND_ASSOC]
	    ]
      ])



val stackSymsPop = store_thm ("stackSymsPop",
``!l pfx.(stackSyms stl = pfx ++ l) ==>
  (stackSyms (pop stl (LENGTH l)) = pfx)``,
SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
`MAP FST (MAP FST stl) = REVERSE l ++ REVERSE pfx` by 
METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
`(MAP FST (MAP FST (pop stl (LENGTH l))) =
  pop (MAP FST (MAP FST stl)) (LENGTH l))` by METIS_TAC [map_pop] THEN
SRW_TAC [] [] THEN
`(pop (REVERSE l ++ REVERSE pfx) (LENGTH l)) =
   REVERSE pfx` by METIS_TAC [popnthm, LENGTH_REVERSE] THEN
SRW_TAC [] [])



val validItemPopStk = store_thm ("validItemPopStk",
``!stl s l. (auggr g st eof = SOME ag) ==>
  validItem ag (stackSyms stl) (item s (l,[])) ==>
 (l' = stackSyms (pop stl (LENGTH l))) ==>
  ((s=startSym ag) \/ ?lhs r1 r2.validItem ag l' 
             (item lhs (r1,NTS s::r2)))``,

SRW_TAC [] [validItem_def] THEN
`?n.NRC (rderives ag) n [NTS (startSym ag)]
            (pfx ++ [NTS s] ++ sfx)` by METIS_TAC [RTC_NRC] THEN
Cases_on `n` THEN
SRW_TAC [] []
THENL[
  FULL_SIMP_TAC (srw_ss()) [NRC, lreseq] THEN
  SRW_TAC [] [],


  `0 < SUC n'` by DECIDE_TAC THEN
  `?m1 m2 pfx1 pfx2 sfx1 sfx2 sfx2' nt'.
           m1 < (SUC n') /\ m2 < (SUC n') /\
           NRC (rderives ag) m1 [NTS (startSym ag)]
             (pfx1 ++ [NTS nt'] ++ sfx1) /\
           MEM (rule nt' (pfx2 ++ [NTS s] ++ sfx2))
             (rules ag) /\ EVERY isTmnlSym sfx1 /\
           NRC (rderives ag) m2
             (pfx1 ++ pfx2 ++ [NTS s] ++ sfx2 ++ sfx1)
             (pfx1 ++ pfx2 ++ [NTS s] ++ sfx2' ++ sfx1) /\
           (pfx = pfx1 ++ pfx2) /\ (sfx = sfx2' ++ sfx1)`
      by METIS_TAC [sublemma] THEN
  SRW_TAC [] [] THEN
  DISJ2_TAC THEN
  MAP_EVERY Q.EXISTS_TAC 
	    [`nt'`, `pfx2`, `sfx2`, `pfx1`, `sfx1`] THEN
	    SRW_TAC [] [] 
	    THENL[
	       METIS_TAC [NRC_RTC],

	       `rderives ag [NTS nt'] (pfx2++[NTS s]++sfx2)` by METIS_TAC [rdres1] THEN
	       `rderives ag (pfx1++[NTS nt']++sfx1) 
        	    (pfx1++pfx2++[NTS s]++sfx2++sfx1)` by METIS_TAC [rderives_append, APPEND_ASSOC] THEN
	       METIS_TAC [APPEND, APPEND_ASSOC],

	       METIS_TAC [APPEND, APPEND_ASSOC],
	       
	       METIS_TAC [stackSymsPop]
	       ]])




val isSuffix_LENGTH = 
store_thm("isSuffix_LENGTH",
``!s l.isSuffix s l ==> (LENGTH l >= LENGTH s)``,
Induct_on `l` THEN SRW_TAC [] [isSuffix_def, IS_PREFIX_NIL, rev_nil] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
`IS_PREFIX (REVERSE l) (REVERSE s) \/
 IS_PREFIX (REVERSE s) (REVERSE l)` by METIS_TAC [IS_PREFIX_APPEND2]
THENL[
      RES_TAC THEN
      FULL_SIMP_TAC (arith_ss) [],

      `(REVERSE s = REVERSE l) \/
       (REVERSE s = REVERSE l ++[h])`  by METIS_TAC [isPfx1]
      THENL[
	    SRW_TAC [] [] THEN
	    `IS_PREFIX (REVERSE l) (REVERSE l)` by METIS_TAC [IS_PREFIX_REFL] THEN
	    RES_TAC THEN
	    `LENGTH s = LENGTH l` by METIS_TAC [rev_len] THEN
	    FULL_SIMP_TAC (arith_ss) [],
	    
	    `LENGTH l = LENGTH (REVERSE l)`
		by METIS_TAC [rev_len] THEN
	    `LENGTH s = LENGTH (REVERSE l ++[h])`
		by METIS_TAC [rev_len] THEN			  
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (arith_ss) []]])

val revEqList = 
store_thm ("revEqList",
``!l1 l2.(REVERSE l1 = REVERSE l2) = (l1=l2)``,
Induct_on `l1` THEN Induct_on `l2` THEN 
SRW_TAC [] [EQ_IMP_THM] THEN
METIS_TAC [last_elem, NOT_CONS_NIL, APPEND_11])

val rtcDerivesInRuleRhsLen = store_thm 
("rtcDerivesInRuleRhsLen",
``!u v.RTC (derives g) u v ==>
  (u=[NTS N]) ==> (LENGTH v > 1) ==> MEM sym v ==>
(?lhs rhs p s.MEM (rule lhs (p++[sym]++s)) (rules g))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
Cases_on `v` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def],

      Cases_on `t` THEN SRW_TAC [] []
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [APPEND_NIL, rgr_r9eq],

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (arith_ss) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	    Cases_on `s1` THEN Cases_on `s2` THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [rgr_r9eq, MEM_APPEND, APPEND, MEM]
	    ]])

val rtcDerivesInRuleRhs = 
store_thm ("rtcDerivesInRuleRhs",
   `` RTC (derives g) [NTS N] (pfx ++ [sym] ++ sfx) ==>
       ~(pfx = []) \/ ~(sfx = []) ==>
       ?lhs rhs p s. MEM (rule lhs (p ++ [sym] ++ s)) (rules g)``,
SRW_TAC [] [] 
THENL[
      Cases_on `pfx` THEN SRW_TAC [] []THEN
      `LENGTH (h::t ++ [sym] ++ sfx) > 1` by (FULL_SIMP_TAC (srw_ss()) [] THEN
					      FULL_SIMP_TAC (arith_ss) []) THEN
      METIS_TAC [rtcDerivesInRuleRhsLen, MEM_APPEND, MEM],

      Cases_on `sfx` THEN SRW_TAC [] []THEN
      `LENGTH (pfx ++ [sym] ++ h::t) > 1` by (FULL_SIMP_TAC (srw_ss()) [] THEN
					      FULL_SIMP_TAC (arith_ss) []) THEN
      METIS_TAC [rtcDerivesInRuleRhsLen, MEM_APPEND, MEM]
      ])


val symInRuleRhsType = store_thm 
("symInRuleRhsType",
``!e r.MEM e (MAP ruleRhs r) ==>
!sym.MEM sym e ==>
(?lhs rhs p s.MEM (rule lhs (p++[sym]++s)) r)``,
Induct_on `r` THEN SRW_TAC [] []
THENL[
      Cases_on `h` THEN
      FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
      METIS_TAC [MEM,rgr_r9eq],
      
      METIS_TAC []
      ])

val rtcRderivesInRuleRhsGen = store_thm 
("rtcRderivesInRuleRhsGen",
``!u v.RTC (rderives g) u v ==>
MEM u (MAP ruleRhs (rules g)) ==>
(LENGTH v >= 1) ==> MEM sym v ==>
(?lhs rhs p s.MEM (rule lhs (p++[sym]++s)) (rules g))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
Cases_on `u` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [rderives_def],

      METIS_TAC [symInRuleRhsType],

      FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [][] THEN
      Cases_on `rules g` THEN
      FULL_SIMP_TAC (srw_ss()) [],

      Cases_on `v` THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      `SUC (LENGTH t') >= 1` by DECIDE_TAC THEN
      `MEM sym (s1 ++ rhs ++ s2)` by SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    Cases_on `s1` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][],

	    METIS_TAC [rgr_r9eq],

	    Cases_on `s1` THEN Cases_on `s2` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [MEM_APPEND,rgr_r9eq,MEM]
	    ]
      ])


val rtcDerivesInRuleRhsGen = store_thm 
("rtcDerivesInRuleRhsGen",
``!u v.RTC (derives g) u v ==>
MEM u (MAP ruleRhs (rules g)) ==>
(LENGTH v >= 1) ==> MEM sym v ==>
(?lhs rhs p s.MEM (rule lhs (p++[sym]++s)) (rules g))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
Cases_on `u` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def],

      METIS_TAC [symInRuleRhsType],

      FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
      FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
      SRW_TAC [][] THEN
      Cases_on `rules g` THEN
      FULL_SIMP_TAC (srw_ss()) [],

      Cases_on `v` THEN
      FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
      `SUC (LENGTH t') >= 1` by DECIDE_TAC THEN
      `MEM sym (s1 ++ rhs ++ s2)` by SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    Cases_on `s1` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][],

	    METIS_TAC [rgr_r9eq],

	    Cases_on `s1` THEN Cases_on `s2` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [MEM_APPEND,rgr_r9eq,MEM]
	    ]
      ])


val auggrFsStNil = store_thm 
("auggrFsStNil",
``(auggr g st eof = SOME ag) ==>
  ~?h.h IN (followSet ag (NTS (startSym ag)))``,

SRW_TAC [] [followSet_def] THEN
Cases_on `~MEM s (MAP ruleRhs (rules ag)) \/
    !pfx sfx.
      ~RTC (derives ag) s
         (pfx ++ [NTS (startSym ag)] ++ [TS ts] ++ sfx)` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(pfx ++ [NTS (startSym ag)] ++ [TS ts] ++ sfx)
= (pfx ++ [NTS (startSym ag)] ++ ([TS ts] ++ sfx))` by SRW_TAC [] [] THEN
`~([TS ts] ++ sfx=[])` by SRW_TAC [] [] THEN
`LENGTH ((pfx ++ [NTS (startSym ag)] ++ [TS ts] ++ sfx)) >=1 `
    by (FULL_SIMP_TAC (srw_ss()) [] THEN
	FULL_SIMP_TAC (arith_ss) []) THEN
`?lhs p s.MEM (rule lhs (p++[NTS (startSym ag)]++s)) (rules ag)`
 by METIS_TAC [rtcDerivesInRuleRhsGen,MEM,MEM_APPEND] THEN
METIS_TAC [auggrStNotInRhs]
)


val cslNotNil = store_thm 
("cslNotNil",
``!l l' h e. (LENGTH (h::t) >= n) ==>
  ~(pop ([h]++t++[e]) n = [])``,
Induct_on `n` THEN SRW_TAC [] [pop_def] THEN
`LENGTH t >= n` by DECIDE_TAC THEN
`LENGTH (t++[e]) > n` by 
(FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC) THEN
METIS_TAC [pop_not_empty])



val sgotoNotNil = store_thm 
("sgotoNotNil",
``MEM (item l (r1,h::r2)) itl ==>
  ~(sgoto ag itl h = [])``,
SRW_TAC [] [sgoto_def, nextState_def] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, md_append, moveDot_def] THEN
METIS_TAC [iclosure_nil, rgr_r9eq, MEM, MEM_APPEND])


val cslInit = store_thm 
("cslInit",
``!l n e.(LENGTH l >= n) ==>
   (pop l n = []) ==>
  (pop (MAP f l ++ [e]) n = [e])``,
Induct_on `l` THEN SRW_TAC [] [pop_def] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
SRW_TAC [] [])



val nullNil = store_thm 
("nullNil",
``!l.(l=[]) = NULL l``,
Induct_on `l` THEN SRW_TAC [] [])
		   
		   
val l1 = store_thm 
("l1",
``!l n e.~(pop l n = []) ==>
   (SND (FST (HD (pop l n))) =
    (SND (HD (pop (MAP FST l ++ [e]) n))))``,
Induct_on `l` THEN SRW_TAC [] [pop_def])



val stackValid = Define
`(stackValid ag ([]:(((symbol#state)#ptree)list)) 
  ([]:((symbol#state)list)) = F) /\
 (stackValid ag [] [e] = EVERY (validItem ag []) (itemlist [e])) /\
 (stackValid ag (x::xs) (y::ys) = 
  EVERY (validItem ag (stackSyms (x::xs))) (itemlist (y::ys)) 
  /\ stackValid ag xs ys) /\
 (stackValid ag _ _ = F)`


val parseInv = Define
`parseInv (ag,(stl:((symbol # state) # ptree) list),csl) = 
validStates ag csl /\
stackValid ag stl csl /\
validStlItemsStack stl csl /\
(validStkSymTree stl)`

val validItemInvReduceStlNil = store_thm(
"validItemInvReduceStlNil",
``validItemInv (ag, stl, csl) ==>
   (csl = MAP FST stl++[(NTS st,initItems ag (rules ag))]) ==>
   EVERY isTmnlSym (h::t) ==>
  (auggr g st eof = SOME ag) ==>
  (doReduce m (h::t,stl,csl) r = SOME (sl',stl',csl')) ==>
 (slr ag = SOME m) ==>
 (stl=[]) ==>
parseInv (ag, stl, csl) ==>
 (getState m (itemlist csl) h = REDUCE r) ==>
 validItemInv (ag,stl',csl')``,
SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION, itemlist_def, parseInv] THEN
 Cases_on `r` THEN 
 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
 SRW_TAC [] [] THEN
 `MEM (item s (l,[])) (initItems ag (rules ag))` by METIS_TAC [getState_mem_itl, validStates_def] THEN
 `MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def] THEN
 `h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
 `validStlItems ([]:((symbol#state)#ptree) list) [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append] THEN
 FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
 `?p.stackSyms ([]:((symbol#state)#ptree) list)  = p++l` by METIS_TAC [isSuffix_APPEND] THEN
 `?x.addRule ([]:((symbol#state)#ptree) list) (rule s l) = SOME x` by METIS_TAC [addRule_SOME] THEN
 `LENGTH ([]:((symbol#state)#ptree) list) >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
 SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackValid, itemlist_def] THEN
`(stackSyms ([]:((symbol#state)#ptree) list)=[])` by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
 `validItem ag (stackSyms ([]:((symbol#state)#ptree) list)) (item s (l,[]))`
     by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF] THEN
 `(s=startSym ag) \/
        ?lhs r1 r2. validItem ag 
         (stackSyms (pop ([]:((symbol#state)#ptree) list) (LENGTH l))) 
         (item lhs (r1,NTS s::r2))` 
     by METIS_TAC [validItemPopStk]
  THENL[
	FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
	SRW_TAC [] [] THEN
	METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

       `IS_PREFIX (REVERSE ([]:((symbol#state)#ptree) list))
            (REVERSE (pop ([]:((symbol#state)#ptree) list) (LENGTH l)))`
	       by METIS_TAC [isPfxRevPopRefl] THEN
	FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
	SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [validItem_def, pop_def] THEN
	 SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
	 `MEM (item lhs ([], NTS s::r2))
              (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
	 FULL_SIMP_TAC (srw_ss()) [doReduce_def, ruleLhs_def, ruleRhs_def, LET_THM, push_def] THEN
	 Cases_on `h` THEN
	 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def, pop_def] THEN	 
	 `~(sgoto ag (initItems ag (rules ag)) (NTS s) = [])` by METIS_TAC [sgotoNotNil] THEN
	 FULL_SIMP_TAC (srw_ss()) [] THEN
	 SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [validItemInv] THEN
	 SRW_TAC [] [] THEN
	 `stk=[((NTS s,
                sgoto ag (initItems ag (rules ag)) (NTS s)),x)]`
	     by (Cases_on `stk` THEN
		 FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND]) THEN
	 SRW_TAC [] [stackSyms_def, stkItl, trans_def, sgoto_def, nextState_def] THEN
	 FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
	 Cases_on `moveDot (initItems ag (rules ag)) (NTS s)`
         THENL[
		SRW_TAC [] []THEN
		FULL_SIMP_TAC (srw_ss()) [iclosure],


		FULL_SIMP_TAC (srw_ss()) []
		]
	 ])


val stkItlEqItemList = store_thm ("stkItlEqItemList",
``!stl n csl e.LENGTH stl >= n ==>
  ~(pop stl n = []) ==>
  (csl = MAP FST stl++[e]) ==>
   (itemlist csl = stkItl stl)``,
Induct_on `n` THEN SRW_TAC [] [] THEN
Cases_on `stl` THEN
FULL_SIMP_TAC (srw_ss()) [pop_def, stkItl, itemlist_def])


val popRevNotNil = 
store_thm ("popRevNotNil",
``!l n.~(pop l n = []) ==>
   ~(REVERSE (pop l n) = [])``,
Induct_on `n` THEN 
Cases_on `l` THEN SRW_TAC [] [pop_def])



val validItemInvReduceStlNotNil = store_thm(
"validItemInvReduceStlNotNil",
``validItemInv (ag, stl, csl) ==>
   (csl = MAP FST stl++[(NTS st,initItems ag (rules ag))]) ==>
   EVERY isTmnlSym (h::t) ==>
  (auggr g st eof = SOME ag) ==>
  (doReduce m (h::t,stl,csl) r = SOME (sl',stl',csl')) ==>
~(stl=[]) ==>
 (slr ag = SOME m) ==>
parseInv (ag,stl,csl) ==>
 (getState m (itemlist csl) h = REDUCE r) ==>
 validItemInv (ag,stl',csl')``,
Cases_on `stl` THEN
SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION, itemlist_def, parseInv, stackValid] THEN
 Cases_on `r` THEN 
 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
 SRW_TAC [] []  THEN
 Cases_on `h'` THEN Cases_on `q` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 `MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl, validStates_def] THEN
 `MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def] THEN
 `h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
 `validStlItems (((q',r'),r)::t') [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append] THEN
 FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
`stackSyms (((q',r'),r)::t') = stackSyms t'++[q']` 
    by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
 `?p.stackSyms (((q',r'),r)::t')  = p++l` by METIS_TAC [isSuffix_APPEND] THEN
 `?x.addRule (((q',r'),r)::t') (rule s l) = SOME x` by METIS_TAC [addRule_SOME] THEN
 `LENGTH (((q',r'),r)::t') >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
 SRW_TAC [] [] THEN
 `validItem ag (stackSyms (((q',r'),r)::t')) (item s (l,[]))`
     by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF] THEN
 `(s=startSym ag) \/
        ?lhs r1 r2. validItem ag 
         (stackSyms (pop (((q',r'),r)::t') (LENGTH l))) 
         (item lhs (r1,NTS s::r2))` 
     by METIS_TAC [validItemPopStk]
  THENL[
	METIS_TAC [auggrFsStNil],

       `IS_PREFIX (REVERSE (((q',r'),r)::t'))
            (REVERSE (pop (((q',r'),r)::t') (LENGTH l)))`
	       by METIS_TAC [isPfxRevPopRefl] THEN
       Cases_on `pop (((q',r'),r)::t') (LENGTH l) = []`
       THENL[
         SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [stackSyms_def, validItem_def] THEN
	 SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [] THEN
	 `MEM (item lhs ([], NTS s::r2))
              (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
	 FULL_SIMP_TAC (srw_ss()) [doReduce_def, ruleLhs_def, ruleRhs_def, LET_THM, push_def] THEN
	 Cases_on `h` THEN
	 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN	 
	 Cases_on `pop
              ((q',r')::
                   (MAP FST t' ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t' ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [] [validItemInv] THEN
	     FULL_SIMP_TAC (srw_ss()) [validItemInv] THEN
	     Cases_on `stk` THEN
	     FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
	     SRW_TAC [] [stackSyms_def, stkItl] THEN
	     `pop (MAP FST (((q',r'),r)::t') ++ [(NTS st,initItems ag (rules ag))]) (LENGTH l)
                      = [(NTS st,initItems ag (rules ag))]` by METIS_TAC [cslInit, addrule_len] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	 FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, trans_def] THEN
	 Cases_on `moveDot (initItems ag (rules ag)) (NTS s)`
         THENL[
		SRW_TAC [] [] THEN
		FULL_SIMP_TAC (srw_ss()) [iclosure],
		FULL_SIMP_TAC (srw_ss()) []
		],	     

	     (* ~ pop stl = [] *)
	 `stkItl (((q',r'),r)::t') = 
           itemlist (MAP FST (((q',r'),r)::t') ++
             [(NTS st,initItems ag (rules ag))])` 
             by METIS_TAC [stkItlEqItemList] THEN
	     FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, ruleLhs_def, ruleRhs_def, push_def] THEN
	     Cases_on `h` THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
	     Cases_on `pop
              ((q',r')::
                   (MAP FST t' ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t' ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     SRW_TAC [] [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [] [] THEN
	     FULL_SIMP_TAC (srw_ss()) [validItemInv] THEN
	     SRW_TAC [] [] THEN
	     `(trans ag (initItems ag (rules ag),
                 stackSyms (REVERSE (REVERSE 
                  (pop (((q',r'),r)::t') (LENGTH l))))) =
               SOME (stkItl (REVERSE (REVERSE (pop (((q',r'),r)::t')
                            (LENGTH l))))))`
	       by METIS_TAC [rev_nil, validItemInv, nullNil] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `MEM (item lhs (r1,NTS s::r2)) 
               (stkItl ((pop (((q',r'),r)::t') 
                        (LENGTH l))))`
		 by METIS_TAC [transImpValidItem] THEN	     
	     SRW_TAC [] [] THEN
	     `IS_PREFIX (REVERSE (pop (((q',r'),r)::t') (LENGTH l))) stk \/
              IS_PREFIX stk (REVERSE (pop (((q',r'),r)::t') (LENGTH l)))` by METIS_TAC [IS_PREFIX_APPEND2]
              THENL[
		`~NULL
                 (REVERSE (pop (((q',r'),r)::t') (LENGTH l)))`
                 by METIS_TAC [popRevNotNil, nullNil] THEN
                FULL_SIMP_TAC (srw_ss()) [] THEN
                `IS_PREFIX (REVERSE (((q',r'),r)::t')) stk`
                  by METIS_TAC [isPfxRevPop] THEN
		FULL_SIMP_TAC (srw_ss()) [],


                `(stk=(REVERSE (pop (((q',r'),r)::t') (LENGTH l))))
                 \/ (stk=(REVERSE (pop (((q',r'),r)::t') (LENGTH l)) ++
              [((NTS s,
                 sgoto ag
                   (SND
                      (HD
                         (pop
                            ((q',r')::
                                 (MAP FST t' ++
                                  [(NTS st,
                                    initItems ag (rules ag))]))
                            (LENGTH l)))) (NTS s)),x)]))`
                    by METIS_TAC [isPfx1]
                 THENL[
                    SRW_TAC [] [],

                    SRW_TAC [] [stackSyms_def, REVERSE_APPEND, stkItl] THEN
		    FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND, stkItl] THEN
		    `MEM (item lhs (r1,NTS s::r2))
                      (SND (FST (HD (pop (((q',r'),r)::t') (LENGTH l)))))`
		    by METIS_TAC [transImpValidItem] THEN
		    SRW_TAC [] [trans_snoc] THEN
		    `~(moveDot
		      (SND (FST (HD (pop (((q',r'),r)::t') (LENGTH l)))))
		      (NTS s) = [])` by (SRW_TAC [] [] THEN
		    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]THEN
		    FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def]) THEN
		    Cases_on `moveDot
		      (SND (FST (HD (pop (((q',r'),r)::t') (LENGTH l)))))
		      (NTS s)` THEN
		    FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
		    IMP_RES_TAC l1 THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN
                    METIS_TAC  [APPEND, APPEND_ASSOC]		    
		    ]
	     ]]])





(* validItem holds after a parse step *)
val parseValidItemInv = store_thm
("parseValidItemInv",
``(slr ag = SOME m) /\ (auggr g st eof = SOME ag) /\
~(sl=[]) /\ EVERY isTmnlSym sl /\
(csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) /\
validItemInv (ag, stl, csl) /\
parseInv (ag,stl,csl) /\
(parse (SOME m) (sl, stl, csl) = SOME (sl',stl',csl'))
 ==> 
validItemInv (ag, stl', csl')``,

SRW_TAC [] [] THEN
      (* (stl=[])*)
      Cases_on `stl` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
        Cases_on `t` THEN
	Cases_on `getState m (initItems ag (rules ag)) h` THEN
	FULL_SIMP_TAC (srw_ss()) []
        THENL[

	      IMP_RES_TAC validItemInvReduceStlNil THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`h`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`g`,`eof`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`stl'`,`sl'`, `r`, `csl'`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [itemlist_def],

	      IMP_RES_TAC validItemInvReduceStlNil THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`h'::t'`,`h`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`g`,`eof`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`stl'`,`sl'`, `r`, `csl'`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [itemlist_def],


	    Cases_on `h` THEN 
	    FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
	    SRW_TAC [] [push_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [validItemInv, tmnlSym_def] THEN
	    SRW_TAC [] [] THEN
	    Cases_on `stk` THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
	    SRW_TAC [] [stackSyms_def, stkItl] THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
	    Cases_on `sgoto ag (initItems ag (rules ag)) (TS s)` THEN
	    Cases_on `reduce ag (initItems ag (rules ag)) (sym2Str (TS s))` THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  Cases_on `LENGTH t=0` THEN
		  FULL_SIMP_TAC (srw_ss()) [],

		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, trans_def] THEN
		  Cases_on `moveDot (initItems ag (rules ag)) (TS s)` THEN
		  FULL_SIMP_TAC (srw_ss()) [iclosure],

		  Cases_on `itemEqRuleList (h::t) (h'::t'')` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ]
	    ],

	Cases_on `h` THEN
	Cases_on `q`  THEN
	FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
	Cases_on `t'` THEN
	Cases_on `getState m r' h'` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	SRW_TAC [] []
        THENL[
	      
	      IMP_RES_TAC validItemInvReduceStlNotNil THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`h'`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`g`,`eof`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`stl'`,`sl'`, `r''`, `csl'`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [itemlist_def],

	      IMP_RES_TAC validItemInvReduceStlNotNil THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`h::t''`,`h'`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`g`,`eof`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN [`stl'`,`sl'`, `r''`, `csl'`] MP_TAC) THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [itemlist_def],

	      Cases_on `h'` THEN 
	      FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
	      SRW_TAC [] [push_def] THEN
	      FULL_SIMP_TAC (srw_ss()) [validItemInv, tmnlSym_def] THEN
	      SRW_TAC [] [] THEN
	      Cases_on `stk` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
	      SRW_TAC [] [] THEN
	      `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	      FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
	      Cases_on `sgoto ag  r' (TS s)` THEN
	      Cases_on `reduce ag  r' (sym2Str (TS s))` THEN
	      FULL_SIMP_TAC (srw_ss()) []
              THENL[
		  Cases_on `LENGTH t'''=0` THEN
		  FULL_SIMP_TAC (srw_ss()) [],


		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [parseInv,stackValid,itemlist_def] THEN
		  `IS_PREFIX (REVERSE t ++ [((q',r'),r)]) (h::t')
                   \/ IS_PREFIX (h::t') (REVERSE t ++ [((q',r'),r)])`
		      by METIS_TAC [IS_PREFIX_APPEND2]
		  THENL[
			RES_TAC THEN
			FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND],
			
			`((REVERSE t ++ [((q',r'),r)])=h::t') 
                         \/ ((REVERSE t ++ [((q',r'),r)] ++
                                      [((TS s,h'::t'''),Leaf (TM s))])=(h::t'))` by METIS_TAC [isPfx1]
			 THENL[
			       `REVERSE (REVERSE t ++ [((q',r'),r)]) = REVERSE (h::t')`
				   by METIS_TAC [] THEN
			       FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
			       RES_TAC THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl,REVERSE_APPEND] THEN
			       SRW_TAC [][],

			       `IS_PREFIX (REVERSE t ++ [((q',r'),r)])
				 (REVERSE t ++ [((q',r'),r)])` by METIS_TAC [IS_PREFIX_REFL] THEN
			       RES_TAC THEN
			       `~NULL (REVERSE t ++ [((q',r'),r)])` by METIS_TAC [popRevNotNil, REVERSE_APPEND, REVERSE, nullNil, MEM, MEM_APPEND] THEN
			       `REVERSE ( h::t') = REVERSE (REVERSE t ++ [((q',r'),r)] ++
						       [((TS s,h'::t'''),Leaf (TM s))])` by METIS_TAC [] THEN
			       FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
			       SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def, stkItl] THEN
			       SRW_TAC [] [trans_snoc] THEN
			       Cases_on `moveDot r' (TS s)` THEN
			       SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, iclosure]
			       ]],



		  Cases_on `itemEqRuleList (h'::t''') (h''::t'''')` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ]]])

val rtcDerivesLastTmnl = store_thm ("rtcDerivesLastTmnl",
``!u v.RTC (derives g) u v ==> (u=(pfx++[TS ts])) ==> 
?pfx'.(v=pfx'++[TS ts])``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN 
SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[
      `[NTS lhs] = [TS ts]` by METIS_TAC [lastElemEq] THEN
      FULL_SIMP_TAC (srw_ss()) [],

      `LAST (s1 ++ [NTS lhs] ++ h::t) = TS ts` by METIS_TAC [last_elem] THEN
      `LAST (h::t) = TS ts` by METIS_TAC [last_append, NOT_CONS_NIL] THEN
      `LAST v' = TS ts` by METIS_TAC [last_append, NOT_CONS_NIL] THEN
      `~(v'=[])` by SRW_TAC [] [] THEN
      METIS_TAC [lastListBdown]])

val lastEofD = store_thm ("lastEofD",
``!g st eof.(auggr g st eof = SOME ag) ==> 
  !l.RTC (derives ag) [NTS (startSym ag)] 
         (pfx++[NTS N]++sfx) ==> 
         ~(N=startSym ag)
  ==> ?pfx'.(sfx = pfx'++[TS eof])``,
SRW_TAC [] [auggr_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1, lreseq, derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
SRW_TAC [] [] THEN
`?pfx'.(pfx ++ [NTS N] ++ sfx)=pfx'++[TS eof]` by METIS_TAC [rtcDerivesLastTmnl, APPEND] THEN
Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`NTS N = TS eof` by METIS_TAC [last_elem] THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [lastListBdown, NOT_CONS_NIL, last_append, last_elem]],
METIS_TAC [slemma1_4, nonTerminalsEq]])



val COND_SOME = store_thm(
  "COND_SOME",
  ``((if P then NONE else x) = SOME y) = 
    ~P /\ (x = SOME y)``,
  SRW_TAC [][]);
val _ = export_rewrites ["COND_SOME"]

val stackSyms_CONS = store_thm(
  "stackSyms_CONS",
  ``stackSyms (((sym, state), tree) :: rest) = 
      stackSyms rest ++ [sym]``,
  SRW_TAC [][stackSyms_def]);
val _ = export_rewrites ["stackSyms_CONS"]

val stackSyms_APPEND = store_thm(
  "stackSyms_APPEND",
  ``stackSyms (x ++ y) = stackSyms y ++ stackSyms x``,
  SRW_TAC [][stackSyms_def, REVERSE_APPEND]);

val getStateGotoMemItl = store_thm
("getStateGotoMemItl",
``(slr ag = SOME m) ==>
MEM (item l (r1,h::r2)) itl ==>
(getState m itl h = GOTO itl') ==>
MEM (item l (r1++[h],r2)) itl'``,
SRW_TAC [] [rgr_r9eq] THEN
`m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag (r1' ++ [item l (r1,h::r2)] ++ r2') h` THEN
Cases_on `reduce ag (r1' ++ [item l (r1,h::r2)] ++ r2') (sym2Str h)` THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[

      Cases_on `LENGTH t` THEN SRW_TAC [] [],

      FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, moveDot_def, md_append] THEN
      METIS_TAC [iclosure_mem, MEM, MEM_APPEND, rgr_r9eq],

      Cases_on `itemEqRuleList (h'::t) (h''::t')` THEN
      FULL_SIMP_TAC (srw_ss()) []
      ])


val isPfxListSeq = store_thm ("isPfxListSeq",
``!l1 rst.IS_PREFIX (l1++rst) l1``,
Induct_on `l1` THEN SRW_TAC [] [IS_PREFIX])


val auggrEofInRhs = store_thm
("auggrEofInRhs",
``(auggr g st eof = SOME ag) ==>
   MEM (rule lhs (p++[TS eof]++s)) (rules ag) ==>
   (lhs=startSym ag) /\ (p=[NTS (startSym g)]) /\ (s=[])``,
SRW_TAC [] [auggr_def,LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def,rules_def] 
THENL[
      METIS_TAC [rgr_r9eq,terminalsEq,slemma1_4Tmnls],

      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [rgr_r9eq,terminalsEq,slemma1_4Tmnls],

      SRW_TAC [][] THEN
      Cases_on `p` THEN Cases_on `s` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [rgr_r9eq,terminalsEq,slemma1_4Tmnls]
      ])



val auggrStRtcRdEofGen = store_thm 
("auggrStRtcRdEofGen",
``!u v.RTC (rderives ag) u v ==>
     (u=[NTS (startSym ag)]) ==>
     MEM (TS eof) v ==>
     (auggr g st eof = SOME ag) ==>
     (?pfx.(v=pfx++[TS eof]) /\ ~MEM (TS eof) pfx)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [][RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def]THEN
SRW_TAC [][]THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      RES_TAC THEN
      `MEM (TS eof) (s1 ++ [NTS lhs] ++ s2)`
      by FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    `(pfx=s1) \/
             (?p s.(s2=p++s) /\ (pfx=s1++[NTS lhs]++p)) \/
             (?p s.(s1=p++s) /\ (pfx=p))`
	    by METIS_TAC [listCompLens] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `s ++ [NTS lhs] ++ s2 = [TS eof]`
		by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) [],

	    `LAST (s1 ++ [NTS lhs] ++ s2)
              = LAST (pfx ++ [TS eof])` by METIS_TAC [] THEN
	    Cases_on `s2=[]` THEN
	    FULL_SIMP_TAC (srw_ss()) []  THEN
	    `LAST (s1++[NTS lhs]++s2) = LAST s2`
	    by METIS_TAC [last_append] THEN
	    `s2=FRONT s2 ++ [LAST s2]` by METIS_TAC [APPEND_FRONT_LAST] THEN
	    SRW_TAC [][] THEN
	    `LAST (pfx++[TS eof]) = LAST [TS eof]`
	    by METIS_TAC [last_append,MEM,MEM_APPEND] THEN
	    FULL_SIMP_TAC (srw_ss()) [LAST] THEN
	    `LAST s2 = TS eof` by METIS_TAC [lastElemEq] THEN
	    SRW_TAC [][] THEN
	    `s1++[NTS lhs]++FRONT s2++[TS eof] = pfx++[TS eof]`
	    by METIS_TAC [APPEND_ASSOC] THEN
	    `s1++[NTS lhs]++FRONT s2=pfx` by METIS_TAC [APPEND_11] THEN
	    METIS_TAC [MEM,MEM_APPEND,rgr_r9eq]
	    ],


      `?p s.rhs=p++[TS eof]++s` by METIS_TAC [rgr_r9eq] THEN
      `(lhs=startSym ag) /\
       (p=[NTS (startSym g)]) /\ (s=[])` by METIS_TAC [auggrEofInRhs] THEN
      SRW_TAC [][] THEN
      `(s1=[]) /\ (s2=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `[NTS (startSym g)]` THEN
      SRW_TAC [][],

      RES_TAC THEN
      `MEM (TS eof) (s1 ++ [NTS lhs] ++ s2)`
      by FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    `(pfx=s1) \/
             (?p s.(s2=p++s) /\ (pfx=s1++[NTS lhs]++p)) \/
             (?p s.(s1=p++s) /\ (pfx=p))`
	    by METIS_TAC [listCompLens] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `s ++ [NTS lhs] ++ s2 = [TS eof]`
		by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) [],


	    Cases_on `MEM (TS eof) rhs` 
	    THENL[
		  
		  `?p s.rhs=p++[TS eof]++s` by METIS_TAC [rgr_r9eq] THEN
		  `(lhs=startSym ag) /\
	           (p=[NTS (startSym g)]) /\ (s=[])` by METIS_TAC [auggrEofInRhs] THEN
		  SRW_TAC [][] THEN
		  `(s1=[]) /\ (s2=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
		  SRW_TAC [][] THEN
		  Q.EXISTS_TAC `[NTS (startSym g)]` THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [],

		  
		  `LAST (s1 ++ [NTS lhs] ++ s2)
                   = LAST (pfx ++ [TS eof])` by METIS_TAC [] THEN
		  Cases_on `s2=[]` THEN
		  FULL_SIMP_TAC (srw_ss()) []  THEN
		  `LAST (s1++[NTS lhs]++s2) = LAST s2`
		      by METIS_TAC [last_append] THEN
		  `s2=FRONT s2 ++ [LAST s2]` by METIS_TAC [APPEND_FRONT_LAST] THEN
		  SRW_TAC [][] THEN
		  `LAST (pfx++[TS eof]) = LAST [TS eof]`
		      by METIS_TAC [last_append,MEM,MEM_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [LAST] THEN
		  `LAST s2 = TS eof` by METIS_TAC [lastElemEq] THEN
		  SRW_TAC [][] THEN
		  `s1++[NTS lhs]++FRONT s2++[TS eof] = pfx++[TS eof]`
		      by METIS_TAC [APPEND_ASSOC] THEN
		  `s1++[NTS lhs]++FRONT s2=pfx` by METIS_TAC [APPEND_11] THEN
		  SRW_TAC [][] THEN
		  Q.EXISTS_TAC `s1++rhs++FRONT s2` THEN
		  SRW_TAC [][] THEN
		  METIS_TAC [APPEND_FRONT_LAST,APPEND_ASSOC,MEM,MEM_APPEND]
		  ]      
	    ]])




val auggrTmSymInBtwn = store_thm 
("auggrTmSymInBtwn",
 ``(auggr g st eof = SOME ag) ==> isTmnlSym h ==>
 RTC (rderives ag) [NTS (startSym ag)] (pfx++[h]++sfx) ==>
     ~(sfx=[]) ==>
     ~(h=TS eof)``,
SRW_TAC [] [] THEN
 Cases_on `~(h=TS eof)`THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
`MEM (TS eof) (pfx++[TS eof]++sfx)` by SRW_TAC [][] THEN
`?pfx'. ((pfx ++ [TS eof] ++ sfx) = pfx' ++ [TS eof]) 
/\ ~MEM (TS eof) pfx'` 
by METIS_TAC [auggrStRtcRdEofGen] THEN
Cases_on `sfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`sfx=FRONT sfx ++ [LAST sfx]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`LAST (pfx'++[TS eof])=LAST [TS eof]` by METIS_TAC [last_append,MEM,MEM_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`LAST sfx = TS eof` by METIS_TAC [lastElemEq,last_append] THEN
`pfx ++ [TS eof] ++ FRONT sfx ++ [TS eof] = pfx' ++ [TS eof]`
    by METIS_TAC [APPEND_ASSOC] THEN
`pfx'=pfx ++ [TS eof] ++ FRONT sfx` by METIS_TAC [APPEND_11] THEN
METIS_TAC [MEM,MEM_APPEND]
)







val transSeqGen = store_thm ("transSeqGen",
``!s s' vp sp' s''.
  (trans g (s, vp) = SOME s') ==>
  (trans g (s',vp') = SOME s'') ==>
  (trans g (s, vp++vp') = SOME s'')``,
Induct_on `vp` THEN SRW_TAC [] [trans_def] THEN
Cases_on `moveDot s h` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) []
)


val transOverAppend = store_thm ("transOverAppend",
``!s0 s vp1 vp2.
(trans ag (s0,vp1++vp2) = SOME s) ==>
 ?s'.(trans ag (s0,vp1) = SOME s') /\
     (trans ag (s',vp2) = SOME s)``,
Induct_on `vp1` THEN Induct_on `vp2` THEN
SRW_TAC [] [trans_def] THEN
Cases_on `moveDot s0 h'` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [trans_def]
)

val transAppend = store_thm ("transAppend",
``!s0 s vp1 vp2.
(trans ag (s0,vp1++vp2) = SOME s) =
 ?s'.(trans ag (s0,vp1) = SOME s') /\
     (trans ag (s',vp2) = SOME s)``,
SRW_TAC [] [EQ_IMP_THM]  THEN
METIS_TAC [transOverAppend,transSeqGen])

val ruleRhsExistsImpTrans = 
store_thm ("ruleRhsExistsImpTrans",
``!r1 r2 s0.MEM (item lhs (r1,r2)) s0 ==>
  ?s'.(trans ag (s0,r2) = SOME s')``,
Induct_on `r2` THEN SRW_TAC [] [trans_def] THEN
Cases_on `moveDot s0 h`THEN
FULL_SIMP_TAC (srw_ss()) [] 
THENL[
      METIS_TAC [MEM,mdMemExists],

      FIRST_X_ASSUM (Q.SPECL_THEN 
			 [`r1++[h]`,
			  `iclosure ag (h'::t)`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `MEM (item lhs (r1 ++ [h],r2))
            (iclosure ag (h'::t))` 
	  by METIS_TAC [mdMemExists,iclosure_mem] THEN
      METIS_TAC []
      ])

val ruleLhsExistsImpTrans = 
store_thm ("ruleLhsExistsImpTrans",
``RTC (rderives ag) [NTS (startSym ag)] (s1++[NTS lhs]++s2) ==>
~(lhs=startSym ag) ==>
EVERY isTmnlSym s2 ==>
MEM (rule lhs rhs) (rules ag) ==>
(slr ag = SOME m) ==>
(auggr g st eof = SOME ag) ==>
(trans ag (initItems ag (rules ag),s1) = SOME itl) ==>
?itl'.(trans ag (initItems ag (rules ag),s1++[NTS lhs]) 
       = SOME itl')``,
SRW_TAC [][] THEN
SRW_TAC [][]THEN
`validItem ag s1 (item lhs ([],rhs))`
by (SRW_TAC [] [validItem_def] THEN
    Q.EXISTS_TAC `s2` THEN
    SRW_TAC [] [] THEN
    METIS_TAC [rdres1,rderives_append,RTC_RULES_RIGHT1]) THEN
`MEM (item lhs ([],rhs)) itl` by METIS_TAC [transImpValidItem] THEN
`?n.NRC (rderives ag) n [NTS (startSym ag)]
(s1++[NTS lhs]++s2)` by METIS_TAC [RTC_NRC] THEN
Cases_on `n` THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
`0 < SUC n'`by DECIDE_TAC THEN
IMP_RES_TAC sublemma THEN
SRW_TAC [][] THEN
`validItem ag (pfx1'++pfx2') (item nt'' (pfx2',[NTS lhs]++sfx2''))`
by (SRW_TAC [] [validItem_def] THEN
    Q.EXISTS_TAC `sfx1'` THEN
    SRW_TAC [] [] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `rderives ag (pfx1' ++ [NTS nt''] ++ sfx1')
      (pfx1' ++ (pfx2' ++ [NTS lhs] ++ sfx2'') ++ sfx1')`
	by METIS_TAC [rdres1,EVERY_APPEND,rderives_append]  THEN
    FULL_SIMP_TAC (srw_ss()) [APPEND_ASSOC] THEN
    METIS_TAC [NRC_RTC]) THEN
`MEM (item nt'' (pfx2',[NTS lhs] ++ sfx2'')) itl`
    by METIS_TAC [transImpValidItem] THEN
SRW_TAC [] [trans_snoc] THEN
Cases_on `trans ag (initItems ag (rules ag),pfx1 ++ pfx2)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `moveDot itl (NTS lhs)` THEN
SRW_TAC [][] THEN
METIS_TAC [mdMemExists,MEM])




val rderivesImpTrans = store_thm ("rderivesImpTrans",
``RTC (rderives ag) [NTS (startSym ag)] (s1++[NTS lhs]++s2) ==>
EVERY isTmnlSym s2 ==>
~(lhs=startSym ag) ==>
MEM (rule lhs rhs) (rules ag) ==>
(slr ag = SOME m) ==>
(auggr g st eof = SOME ag) ==>
(trans ag (initItems ag (rules ag),s1) = SOME itl) ==>
?itl'.(trans ag (initItems ag (rules ag),s1++rhs) = SOME itl')``,
SRW_TAC [][]THEN
`validItem ag s1 (item lhs ([],rhs))`
by (SRW_TAC [] [validItem_def] THEN
    Q.EXISTS_TAC `s2` THEN
    SRW_TAC [] [] THEN
    METIS_TAC [rdres1,rderives_append,RTC_RULES_RIGHT1]) THEN
IMP_RES_TAC ruleLhsExistsImpTrans THEN
FULL_SIMP_TAC (srw_ss()) [transAppend] THEN
`MEM (item lhs ([],rhs)) s'` by METIS_TAC [transImpValidItem] THEN
METIS_TAC [ruleRhsExistsImpTrans,transSeqGen,transAppend,transOutEq]
)



val rtcRdImpTrans = 
store_thm ("rtcRdImpTrans",
``!u v.RTC (rderives ag) u v ==>
   (u=[NTS (startSym ag)]) ==>
   !pfx N sfx.(v=pfx++[NTS N]++sfx) ==>
   ~(N=startSym ag) ==>
   (auggr g st eof = SOME ag) ==>
   (slr ag = SOME m) ==>
   ?itl.(trans ag (initItems ag (rules ag),pfx) 
= SOME itl)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [lreseq],

      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [][] THEN
      Cases_on `lhs=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    `(s1=[]) /\ (s2=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [rderives_def,lreseq] THEN
	    `rhs=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
	    SRW_TAC [][] THEN
	    Cases_on `pfx` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
            THENL[
		  `MEM (item (startSym ag) ([],[NTS (startSym g);TS eof]))
            	    (initItems ag (rules ag))` 
		      by METIS_TAC [auggrExistsMemInit,initItems_def,iclosure_mem] THEN
		  SRW_TAC [] [trans_def] THEN
		  Cases_on `moveDot (initItems ag (rules ag)) (NTS (startSym g))` THEN
		  SRW_TAC [] [] ,

		  Cases_on `t` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ],


	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN 
			       [`s1`,`lhs`,`s2`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [rderives_def]THEN
	    SRW_TAC [][] THEN
	    `(pfx = s1++rhs) \/
         (?pfx' sfx'.
            (s1++rhs = pfx ++ [NTS N] ++ pfx') /\ (sfx = pfx' ++ sfx')) \/
         ?pfx' sfx'. (pfx = pfx' ++ sfx') /\ (s1++rhs = pfx')`
	    by METIS_TAC [listCompLens,APPEND_ASSOC] THEN
	    SRW_TAC [][]
	    THENL[
		  `s2=[NTS N]++sfx` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],


		  `s2=sfx'` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		  SRW_TAC [][] THEN
		  `(pfx = s1) \/
		      (?p s.
			(s1 = pfx ++ [NTS N] ++ p) /\ (pfx' = p ++ s)) \/
		      ?p s. (pfx = p ++ s) /\ (s1 = p)` by METIS_TAC [listCompLens] THEN
		  SRW_TAC [][]
		  THENL[
			METIS_TAC [transAppend,APPEND_ASSOC],

			`rhs=s++[NTS N]++pfx'` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
			SRW_TAC [][] THEN
			IMP_RES_TAC rderivesImpTrans THEN
			METIS_TAC [APPEND_ASSOC,transAppend]
			],


		  `s2=sfx'++[NTS N]++sfx`
		      by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
		  ]]])


val slrTransConf = store_thm
("slrTransConf",
``(slr ag = SOME m) ==>
   validItl ag itl ==>
   isTmnlSym h ==>
  (auggr g st eof = SOME ag) ==>
  (trans ag (initItems ag (rules ag),pfx) = SOME itl) ==>
  (getState m itl h = REDUCE r) ==>
  !sfx.~?itl'.(trans ag (initItems ag (rules ag),pfx++h::sfx)
		= SOME itl')``,
SRW_TAC [] [transAppend] THEN
Cases_on `r` THEN
`MEM (item s (l,[])) itl` by METIS_TAC [sgoto_exp,getState_mem_itl] THEN
`h IN (followSet ag (NTS s))` by METIS_TAC [sgoto_exp,getState_reduce_followSet] THEN
Cases_on `~(trans ag (itl,h::sfx) = SOME itl')` THEN
FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
Cases_on `moveDot itl h` THEN
FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`itl`,`h`] MP_TAC) THEN
SRW_TAC [][]  THEN
Cases_on `sgoto ag itl h` THEN
Cases_on `reduce ag itl (sym2Str h)` THEN
SRW_TAC [][]
THENL[
      METIS_TAC [reduce_not_mem],

      Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
      METIS_TAC [iclosure_mem,MEM],

      METIS_TAC [reduce_not_mem],

      Cases_on `t''` THEN SRW_TAC [][]
      ])
	    


val vpPropValidItemThmStlNotNil = store_thm 
("vpPropValidItemThmStlNotNil",
``!m g.(auggr g st eof = SOME ag) ==>
(slr ag = SOME m) ==> 
~(stl=[]) ==>
~(exitCond (eof,NTS (startSym g)) (ininp,stl,csl)) ==>
RTC (rderives ag) [NTS (startSym ag)] ((stackSyms stl)++ininp) ==>
RTC (rderives ag) ((stackSyms stl)++ininp) (onstk++ininp) ==>
EVERY isTmnlSym (onstk++ininp) ==>
(onstk = stacktreeleaves (REVERSE stl)) ==>
(sl=onstk++ininp) ==>
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
validItemInv (ag, stl, csl) ==>
parseInv (ag, stl, csl) ==>
viablePfx ag (N,h) (stackSyms stl++ininp) (stackSyms stl) ==>
((parse (SOME m) (ininp, stl, csl) = SOME (sl',stl',csl'))) ==>
?N' h'.viablePfx ag (N',h') (stackSyms stl'++sl') 
       (stackSyms stl')``,

SRW_TAC [] [] THEN
Cases_on `stl` THEN
SRW_TAC [] [] THEN
Cases_on `h'` THEN Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
Cases_on `ininp` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t'` THEN Cases_on `getState m r' h'` THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
  Q.PAT_ASSUM `doReduce X Y Z = SOME Q` MP_TAC THEN 
  ASM_SIMP_TAC (srw_ss()) [doReduce_def, SYM sym_r1b, LET_THM] THEN
  Cases_on `addRule (((q',r'),r)::t) r''` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN 
  Q.ABBREV_TAC 
    `precsl = pop ((q',r'):: (MAP FST t ++
                              [(NTS st, initItems ag (rules ag))]))
                  (LENGTH (ruleRhs r''))` THEN 
  Q.ABBREV_TAC `precsl_topstate = FST m (SND (HD precsl))` THEN 
  Q.ABBREV_TAC 
     `prestl = pop (((q',r'), r)::t) (LENGTH (ruleRhs r''))` THEN 
  SRW_TAC [][] THEN 
  `?M rhs. r'' = rule M rhs` 
     by METIS_TAC [TypeBase.nchotomy_of ``:rule``] THEN 
  SRW_TAC [][] THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def] THEN 
  `pfx ++ h = stackSyms t ++ [q']`
     by (SPOSE_NOT_THEN ASSUME_TAC THEN 
	 `?l. ~(l = []) /\ (stackSyms t ++ [q'] ++ l = pfx ++ h)`
            by METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL] THEN
`(?l1 l2.(l=l1++l2) /\
(pfx=stackSyms t ++ [q']++l1) /\
(h=l2)) \/
(?h1 h2.(h=h1++h2) /\
(stackSyms t ++ [q'] = pfx++h1) /\
 (l=h2)) \/
((stackSyms t ++ [q'] = pfx) /\ 
(l=h))` by (SRW_TAC [] [] THEN
`?l1 l2.(pfx=stackSyms t ++[q'] ++l1) /\ (h=l2) /\
 (l=l1++l2) \/
 (h=l2++[q']++l) /\ (pfx=l1) /\
 (stackSyms t = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [] [])
THENL[

SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv] THEN
`validStlItems (((q',r'),r)::t) r'` by METIS_TAC [parseInv, SND, HD, itemlist_def,stackValid] THEN
`validStlItems (((q',r'),r)::t) [item M (rhs,[])]` by METIS_TAC [rgr_r9eq, validStlItems_append, getState_mem_itl, sgoto_exp, parseInv, stackValid, validStates_def] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
`h' = HD (l1++h++sfx)` by METIS_TAC [APPEND_11, HD,  APPEND, APPEND_ASSOC] THEN
`MEM (rule M rhs) (rules ag)` by METIS_TAC [getstate_red, sgoto_exp, parseInv, validStates_def, stackValid] THEN
`~(l1++h++sfx=[])` by SRW_TAC [] [] THEN
`l1++h++sfx=h'::TL (l1++h++sfx)` by METIS_TAC [CONS, nullNil] THEN
`RTC (rderives ag) [NTS (startSym ag)]
            ((stackSyms t ++ [q']) ++ [h']++(TL (l1 ++ h ++ sfx)))`
    by METIS_TAC [APPEND_ASSOC, APPEND] THEN
`~(stackSyms t ++[q'] = [])`by SRW_TAC [] [] THEN
`?lhs rhs p s. MEM (rule lhs (p ++ [h'] ++ s)) (rules ag)`
    by METIS_TAC [rtcRderivesInRuleRhs, APPEND_ASSOC, APPEND_NIL] THEN
`h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
SRW_TAC [][] THEN
`REVERSE (((q',r'),r)::t) = (REVERSE t ++ [((q',r'),r)])`
    by SRW_TAC [][REVERSE_APPEND] THEN
`(trans ag
        (initItems ag (rules ag),
         stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
         SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv] THEN
FULL_SIMP_TAC (srw_ss()) [stkItl,REVERSE_APPEND,stackSyms_def] THEN
`REVERSE (MAP FST (MAP FST t)) ++ [q'] ++
           [HD (l1 ++ h ++ sfx)] =
           REVERSE (MAP FST (MAP FST t)) ++ [q'] ++
		   [HD (l1 ++ h ++ sfx)]++TL (l1 ++ h ++ sfx)`
by METIS_TAC [APPEND,APPEND_ASSOC] THEN
`TL (l1 ++ h ++ sfx) = []` by METIS_TAC [APPEND_11,APPEND_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`[HD (l1 ++ h ++ sfx)]=[TS eof]` by METIS_TAC [RTC_RTC,auggrStRtcRdEof,EVERY_APPEND,EVERY_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
`(lhs = startSym ag) /\ (p = [NTS (startSym g)]) /\
       (s = [])` by METIS_TAC [auggrEofInRhs] THEN
SRW_TAC [][] THEN
Cases_on `l1` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `N=startSym ag` THEN
SRW_TAC [][]
THENL[
      METIS_TAC [APPEND,NOT_CONS_NIL,auggrStartRule],

      METIS_TAC [MEM,MEM_APPEND,APPEND_NIL,lastEof],

      METIS_TAC [APPEND_ASSOC,MEM,MEM_APPEND,auggrRtcRderivesPfxSfxNil],
      
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      METIS_TAC [MEM,MEM_APPEND,APPEND_NIL,lastEof],

      Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      METIS_TAC [APPEND_ASSOC,MEM,MEM_APPEND,auggrRtcRderivesPfxSfxNil],

      Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) []
      ],


SRW_TAC [] [] THEN
`MEM (rule M rhs) (rules ag)` by METIS_TAC [getstate_red, sgoto_exp, parseInv, validStates_def] THEN
`~(stackSyms t ++[q'] = [])`by SRW_TAC [] [] THEN
`?lhs rhs p s. MEM (rule lhs (p ++ [h'] ++ s)) (rules ag)`
    by METIS_TAC [rtcRderivesInRuleRhs, APPEND_ASSOC, APPEND_NIL] THEN
`h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
`h'=TS eof`by METIS_TAC [RTC_RTC,auggrStRtcRdEof,EVERY_DEF,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
SRW_TAC [][] THEN
`h2++sfx=[TS eof]` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
Cases_on `h2`THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]THEN
Cases_on `N=startSym ag` THEN
SRW_TAC [] []
THENL[
      `pfx=[]` by METIS_TAC [auggrRtcRderivesPfxSfxNil,APPEND_NIL] THEN
      SRW_TAC [][] THEN
      `h1++[TS eof]=[NTS (startSym g); TS eof]`
      by METIS_TAC [auggrStartRule] THEN
      Cases_on `h1` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t'` THEN
      FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [APPEND_NIL,MEM,MEM_APPEND,lastEof]
      ],


SRW_TAC [] [] THEN
`MEM (rule M rhs) (rules ag)` by METIS_TAC [getstate_red, sgoto_exp, parseInv, validStates_def] THEN
`~(stackSyms t ++[q'] = [])`by SRW_TAC [] [] THEN
`?lhs rhs p s. MEM (rule lhs (p ++ [h'] ++ s)) (rules ag)`
    by METIS_TAC [rtcRderivesInRuleRhs, APPEND_ASSOC, APPEND_NIL] THEN
`h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
`[h']=h++sfx` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `N=startSym ag` THEN
SRW_TAC [][]
THENL[
      METIS_TAC [MEM,MEM_APPEND,APPEND_NIL,auggrRtcRderivesPfxSfxNil],

      METIS_TAC [MEM,MEM_APPEND,APPEND_NIL,lastEof]
      ]
]) THEN

SRW_TAC [] [] THEN
`[h']=sfx` by METIS_TAC [APPEND_11]THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parseInv,stackValid,itemlist_def] THEN
`(stackSyms (((q',r'),r)::t)) = (stackSyms t ++ [q'])` 
    by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
`validItem ag (stackSyms (((q',r'),r)::t)) (item M (rhs,[]))`
by METIS_TAC [SND, HD, itemlist_def, EVERY_DEF, EVERY_APPEND,
rgr_r9eq, getState_mem_itl, sgoto_exp, validStates_def, parseInv] THEN
`(M=startSym ag) \/
 ?lhs r1 r2. validItem ag (stackSyms prestl) (item lhs (r1,NTS M::r2))`
by METIS_TAC [validItemPopStk, ruleRhs_def]
THENL[
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv,exitCond_def] THEN
      `validStlItems (((q',r'),r)::t) r'` by METIS_TAC [parseInv, SND, HD, itemlist_def] THEN
      `validStlItems (((q',r'),r)::t) [item (startSym ag) (rhs,[])]` by METIS_TAC [rgr_r9eq, validStlItems_append, getState_mem_itl, sgoto_exp, parseInv, validStates_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
      FULL_SIMP_TAC (srw_ss()) [isSuffix_def, REVERSE_APPEND] THEN
      `rhs=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule, getstate_red, sgoto_exp, parseInv, validStates_def] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, IS_PREFIX] THEN
      SRW_TAC [][] THEN
      METIS_TAC [auggrTmSymInBtwn,APPEND,NOT_CONS_NIL,isTmnlSym_def],



      `~NULL (REVERSE (((q',r'),r)::t))` 
	  by METIS_TAC [rev_nil, nullNil, NOT_CONS_NIL] THEN
      `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))` 
	  by METIS_TAC [validItemInv, IS_PREFIX_REFL] THEN
      `validItem ag (stackSyms (REVERSE (REVERSE (((q',r'),r)::t))))
                    (item N (h,[]))` by (
        SRW_TAC [] [validItem_def] THEN
      MAP_EVERY Q.EXISTS_TAC [`pfx`,`[h']`] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [rdres1, rderives_append, EVERY_DEF]) THEN
      FULL_SIMP_TAC (srw_ss()) [stkItl, REVERSE_REVERSE] THEN
      `MEM (item N (h,[])) r'` by METIS_TAC [transImpValidItem] THEN
      `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
      `h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
      `MEM (item M (rhs,[])) r'` by METIS_TAC [sgoto_exp, getState_mem_itl,validStates_def, parseInv] THEN
      `(item M (rhs,[]) = item N (h,[]))`  
	  by METIS_TAC [slrCompItemsEq, completeItem_def,
			itemLhs_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `([NTS (startSym ag)] =
             (pfx ++ [NTS M] ++ [h'])) \/
       ?u.RTC (rderives ag) [NTS (startSym ag)] u /\
          rderives ag u (pfx++[NTS M]++[h'])` 
	  by METIS_TAC [RTC_CASES2] 
      THENL[
	    Cases_on `pfx` THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
	    SRW_TAC [] [] THEN
	    MAP_EVERY Q.EXISTS_TAC [`lhs'`, `rhs`, `s1`, `s2`] THEN
	    SRW_TAC [] [ruleLhs_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] 
	    THENL[
		  `stackSyms (((q',r'),r)::t) = pfx++h`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND] THEN
		  METIS_TAC [stackSymsPop, APPEND_11, APPEND, APPEND_ASSOC],

		  `stackSyms (((q',r'),r)::t) = pfx++h`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND] THEN
		  `stackSyms prestl = pfx` by METIS_TAC [stackSymsPop, ruleRhs_def] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
		  METIS_TAC [list_isp, APPEND_ASSOC, EVERY_DEF]
		  ]
	    ]
      ],



(* doReduce, more than one *)


  Q.PAT_ASSUM `doReduce X Y Z = SOME Q` MP_TAC THEN 
  ASM_SIMP_TAC (srw_ss()) [doReduce_def, SYM sym_r1b, LET_THM] THEN
  Cases_on `addRule (((q',r'),r)::t) r''` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN 
  Q.ABBREV_TAC 
    `precsl = pop ((q',r'):: (MAP FST t ++
                              [(NTS st, initItems ag (rules ag))]))
                  (LENGTH (ruleRhs r''))` THEN 
  Q.ABBREV_TAC `precsl_topstate = FST m (SND (HD precsl))` THEN 
  Q.ABBREV_TAC 
     `prestl = pop (((q',r'), r)::t) (LENGTH (ruleRhs r''))` THEN 
  SRW_TAC [][] THEN 
  `?M rhs. r'' = rule M rhs` 
     by METIS_TAC [TypeBase.nchotomy_of ``:rule``] THEN 
  SRW_TAC [][] THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def] THEN 
  `pfx ++ h = stackSyms t ++ [q']`
     by (SPOSE_NOT_THEN ASSUME_TAC THEN 
	 `?l. ~(l = []) /\ (stackSyms t ++ [q'] ++ l = pfx ++ h)`
            by METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL] THEN
`(?l1 l2.(l=l1++l2) /\
(pfx=stackSyms t ++ [q']++l1) /\
(h=l2)) \/
(?h1 h2.(h=h1++h2) /\
(stackSyms t ++ [q'] = pfx++h1) /\
 (l=h2)) \/
((stackSyms t ++ [q'] = pfx) /\ 
(l=h))` by (SRW_TAC [] [] THEN
`?l1 l2.(pfx=stackSyms t ++[q'] ++l1) /\ (h=l2) /\
 (l=l1++l2) \/
 (h=l2++[q']++l) /\ (pfx=l1) /\
 (stackSyms t = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [] [])
THENL[

      SRW_TAC [] []THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv] THEN
      `validStlItems (((q',r'),r)::t) r'` by METIS_TAC [parseInv, SND, HD, itemlist_def] THEN
      `validStlItems (((q',r'),r)::t) [item M (rhs,[])]` by METIS_TAC [rgr_r9eq, validStlItems_append, getState_mem_itl, sgoto_exp, parseInv, validStates_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
      `h' = HD (l1++h++sfx)` by METIS_TAC [APPEND_11, HD,  APPEND, APPEND_ASSOC] THEN
      `MEM (rule M rhs) (rules ag)` by METIS_TAC [getstate_red, sgoto_exp, parseInv, validStates_def] THEN
      `~(l1++h++sfx=[])` by SRW_TAC [] [] THEN
      `l1++h++sfx=h'::TL (l1++h++sfx)` by METIS_TAC [CONS, nullNil] THEN
      `RTC (rderives ag) [NTS (startSym ag)]
			 ((stackSyms t ++ [q']) ++ [h']++(TL (l1 ++ h ++ sfx)))`
	  by METIS_TAC [APPEND_ASSOC, APPEND] THEN
      `~(stackSyms t ++[q'] = [])`by SRW_TAC [] [] THEN
      `?lhs rhs p s. MEM (rule lhs (p ++ [h'] ++ s)) (rules ag)`
	  by METIS_TAC [rtcRderivesInRuleRhs, APPEND_ASSOC, APPEND_NIL] THEN
      `h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
      `stackSyms t ++ [q'] ++ [h']++ h''::t'' =
       stackSyms t ++ [q'] ++ [h'] ++ TL (l1++h++sfx)`
	  by METIS_TAC [APPEND,APPEND_ASSOC] THEN
      `h''::t'' = TL (l1++h++sfx)` by METIS_TAC [APPEND_11] THEN
      SRW_TAC [][]THEN
      Cases_on `N=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    METIS_TAC [MEM,MEM_APPEND,auggrRtcRderivesPfxSfxNil,APPEND_ASSOC],

	    SRW_TAC [][] THEN
	    `REVERSE (((q',r'),r)::t) = (REVERSE t ++ [((q',r'),r)])`
		by SRW_TAC [][REVERSE_APPEND] THEN
	    `(trans ag
		    (initItems ag (rules ag),
		     stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
		    SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
		by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl,REVERSE_APPEND,stackSyms_def] THEN
	    SRW_TAC [][] THEN
	    `?itl.trans ag (initItems ag (rules ag), 
			    REVERSE (MAP FST (MAP FST t)) ++ [q'] ++ l1) = 
              SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
	    Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [slrTransConf,parseInv,validStates_def],

	    METIS_TAC [MEM,MEM_APPEND,auggrRtcRderivesPfxSfxNil,APPEND_ASSOC],
	    
	    SRW_TAC [][] THEN
	    `REVERSE (((q',r'),r)::t) = (REVERSE t ++ [((q',r'),r)])`
		by SRW_TAC [][REVERSE_APPEND] THEN
	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
              SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
		by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl,REVERSE_APPEND,stackSyms_def] THEN
	    SRW_TAC [][] 
            THENL[
		  `?itl.trans ag (initItems ag (rules ag), 
				  REVERSE (MAP FST (MAP FST t)) ++ [q'] ++ l1) = 
                      SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
		  Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [slrTransConf,parseInv,validStates_def],

		  Cases_on `h` THEN Cases_on `l1` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  THENL[
		  `validItem ag (REVERSE (MAP FST (MAP FST t)) ++ [q'])
	          (item N ([],h'::t'))`
		      by (SRW_TAC [][validItem_def] THEN
			  Q.EXISTS_TAC `sfx` THEN SRW_TAC [][] THEN
			  METIS_TAC [rdres1,rderives_append]) THEN
		  `MEM (item N ([],h'::t')) r'`  by METIS_TAC [transImpValidItem] THEN
		  `((item N ([],h'::t')) = item M (rhs,[])) \/
                   ~ ?l' r2 r1. (item N ([],h'::t')) = item l' (r1,h'::r2)` by 
									    METIS_TAC [parseInv,validStates_def,shiftReduce] THEN
		  FULL_SIMP_TAC (srw_ss()) [],
		  
		  `?itl.trans ag (initItems ag (rules ag), 
				  REVERSE (MAP FST (MAP FST t)) ++ [q'] ++ h::t''') = 
                  SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
		  METIS_TAC [slrTransConf,parseInv,validStates_def]
		  ],

	    Cases_on `h` THEN Cases_on `l1` THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  `validItem ag (REVERSE (MAP FST (MAP FST t)) ++ [q'])
	           (item N ([],h'::t'))`
		      by (SRW_TAC [][validItem_def] THEN
			  Q.EXISTS_TAC `sfx` THEN SRW_TAC [][] THEN
			  METIS_TAC [rdres1,rderives_append]) THEN
		  `MEM (item N ([],h'::t')) r'`  by METIS_TAC [transImpValidItem] THEN
		  `((item N ([],h'::t')) = item M (rhs,[])) \/
                   ~ ?l' r2 r1. (item N ([],h'::t')) = item l' (r1,h'::r2)` by 
		   METIS_TAC [parseInv,validStates_def,shiftReduce] THEN
		  FULL_SIMP_TAC (srw_ss()) [],

		  `?itl.trans ag (initItems ag (rules ag), 
				  REVERSE (MAP FST (MAP FST t)) ++ [q'] ++ h::t''') = 
                   SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
		  METIS_TAC [slrTransConf,parseInv,validStates_def]
		  ]
	    ]],


      SRW_TAC [] [] THEN
      `MEM (rule M rhs) (rules ag)` by METIS_TAC [getstate_red, sgoto_exp, parseInv, validStates_def] THEN
      `~(stackSyms t ++[q'] = [])`by SRW_TAC [] [] THEN
      `?lhs rhs p s. MEM (rule lhs (p ++ [h'] ++ s)) (rules ag)`
	  by METIS_TAC [rtcRderivesInRuleRhs, APPEND_ASSOC, APPEND] THEN
      `h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
      SRW_TAC [][] THEN
      `REVERSE (((q',r'),r)::t) = (REVERSE t ++ [((q',r'),r)])`
	  by SRW_TAC [][REVERSE_APPEND] THEN
      `(trans ag
        (initItems ag (rules ag),
         stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
        SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
	  by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv] THEN
      FULL_SIMP_TAC (srw_ss()) [stkItl,REVERSE_APPEND,stackSyms_def] THEN
      SRW_TAC [][] THEN
      Cases_on `h2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `validItem ag (REVERSE (MAP FST (MAP FST t)) ++ [q'])
        (item N (h1,h::t'))`
	  by (SRW_TAC [][validItem_def] THEN
	      Q.EXISTS_TAC `sfx` THEN SRW_TAC [][] THEN
	      METIS_TAC [rdres1,rderives_append,APPEND_ASSOC]) THEN
      `MEM (item N (h1,h::t')) r'` by METIS_TAC [transImpValidItem] THEN
      `h'::h''::t'' = h::t'++sfx` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) []THEN
      SRW_TAC [][] THEN
      METIS_TAC [sgoto_exp,slrNotValid,getState_mem_itl,parseInv,validStates_def],

      SRW_TAC [] [] THEN
      `MEM (rule M rhs) (rules ag)` by METIS_TAC [getstate_red, sgoto_exp, parseInv, validStates_def] THEN
      `h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
      `REVERSE (((q',r'),r)::t) = (REVERSE t ++ [((q',r'),r)])`
	  by SRW_TAC [][REVERSE_APPEND] THEN
      `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
              SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
    by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv] THEN
      FULL_SIMP_TAC (srw_ss()) [stkItl,REVERSE_APPEND,stackSyms_def] THEN
      SRW_TAC [][] THEN
      Cases_on `h` THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `validItem ag (REVERSE (MAP FST (MAP FST t)) ++ [q'])
         (item N ([],h'''::t'))`
	  by (SRW_TAC [][validItem_def] THEN
	Q.EXISTS_TAC `sfx` THEN SRW_TAC [][] THEN
	METIS_TAC [rdres1,rderives_append]) THEN
      `h'::h''::t'' = h'''::t' ++ sfx`
	  by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      `MEM (item N ([],h'::t')) r'`  by METIS_TAC [transImpValidItem] THEN
      `((item N ([],h'::t')) = item M (rhs,[])) \/
			    ~ ?l' r2 r1. (item N ([],h'::t')) = item l' (r1,h'::r2)` 
	  by  METIS_TAC [parseInv,validStates_def,shiftReduce]  THEN
      FULL_SIMP_TAC (srw_ss()) []
      ]) THEN
SRW_TAC [] [] THEN
`h'::h''::t''=sfx` by METIS_TAC [APPEND_11] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parseInv,stackValid,itemlist_def] THEN
`(stackSyms (((q',r'),r)::t)) = (stackSyms t ++ [q'])`
    by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
`validItem ag (stackSyms (((q',r'),r)::t)) (item M (rhs,[]))`
by METIS_TAC [SND, HD, itemlist_def, EVERY_DEF, EVERY_APPEND,
rgr_r9eq, getState_mem_itl, sgoto_exp, validStates_def, parseInv] THEN
`(M=startSym ag) \/
 ?lhs r1 r2. validItem ag (stackSyms prestl) (item lhs (r1,NTS M::r2))`
by METIS_TAC [validItemPopStk, ruleRhs_def]
THENL[
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv] THEN
      `validStlItems (((q',r'),r)::t) r'` 
	  by METIS_TAC [parseInv, SND, HD, itemlist_def] THEN
      `validStlItems (((q',r'),r)::t) [item (startSym ag) (rhs,[])]` by METIS_TAC [rgr_r9eq, validStlItems_append, getState_mem_itl, sgoto_exp, parseInv, validStates_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
      FULL_SIMP_TAC (srw_ss()) [isSuffix_def, REVERSE_APPEND] THEN
      `rhs=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule, getstate_red, sgoto_exp, parseInv, validStates_def] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, IS_PREFIX,exitCond_def] THEN
            SRW_TAC [][] THEN
      METIS_TAC [auggrTmSymInBtwn,APPEND,NOT_CONS_NIL,isTmnlSym_def],

      `~NULL (REVERSE (((q',r'),r)::t))` 
	  by METIS_TAC [rev_nil, nullNil, NOT_CONS_NIL] THEN
      `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))` 
	  by METIS_TAC [validItemInv, IS_PREFIX_REFL] THEN
      `validItem ag (stackSyms (REVERSE (REVERSE (((q',r'),r)::t))))
                    (item N (h,[]))` by (
        SRW_TAC [] [validItem_def] THEN
      MAP_EVERY Q.EXISTS_TAC [`pfx`,`h'::h''::t''`] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [rdres1, rderives_append, EVERY_DEF]) THEN
      FULL_SIMP_TAC (srw_ss()) [stkItl, REVERSE_REVERSE] THEN
      `MEM (item N (h,[])) r'` by METIS_TAC [transImpValidItem] THEN
      `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
      `h' IN (followSet ag (NTS M))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv] THEN
      `MEM (item M (rhs,[])) r'` by METIS_TAC [sgoto_exp, getState_mem_itl,validStates_def, parseInv] THEN
      `(item M (rhs,[]) = item N (h,[]))`  
	  by METIS_TAC [slrCompItemsEq, completeItem_def,
			itemLhs_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `([NTS (startSym ag)] =
             (pfx ++ [NTS M] ++ h'::h''::t'')) \/
       ?u.RTC (rderives ag) [NTS (startSym ag)] u /\
          rderives ag u (pfx++[NTS M]++h'::h''::t'')` 
	  by METIS_TAC [RTC_CASES2] 
      THENL[
	    Cases_on `pfx` THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
	    SRW_TAC [] [] THEN
	    MAP_EVERY Q.EXISTS_TAC [`lhs'`, `rhs`, `s1`, `s2`] THEN
	    SRW_TAC [] [ruleLhs_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] 
	    THENL[
		  `stackSyms (((q',r'),r)::t) = pfx++h`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND] THEN
		  METIS_TAC [stackSymsPop,APPEND_11, APPEND_ASSOC, APPEND],

		  `stackSyms (((q',r'),r)::t) = pfx++h`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND] THEN
		  `stackSyms prestl = pfx` by METIS_TAC [stackSymsPop, ruleRhs_def] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
		  METIS_TAC [list_isp, APPEND_ASSOC, EVERY_DEF]
		  ]
	    ]
      ],


(* GOTO l *)
FULL_SIMP_TAC (srw_ss()) [push_def, viablePfx_def, handleg_def] THEN
SRW_TAC [] [] THEN
`~(pfx ++ h = stackSyms t ++ [q'])`
    by (SPOSE_NOT_THEN ASSUME_TAC THEN 
SRW_TAC [] []THEN
`h'::h''::t'' = sfx` by METIS_TAC [APPEND_11] THEN
SRW_TAC [] [] THEN
`h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
`~NULL (REVERSE (((q',r'),r)::t))` 
	  by METIS_TAC [rev_nil, nullNil, NOT_CONS_NIL] THEN
      `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))` 
	  by METIS_TAC [validItemInv, IS_PREFIX_REFL] THEN
      `validItem ag (stackSyms (REVERSE (REVERSE (((q',r'),r)::t))))
                    (item N (h,[]))` by (
        SRW_TAC [] [validItem_def] THEN
      MAP_EVERY Q.EXISTS_TAC [`pfx`,`h'::h''::t''`] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [rdres1, rderives_append, EVERY_DEF]) THEN
      FULL_SIMP_TAC (srw_ss()) [stkItl, REVERSE_REVERSE] THEN
      `MEM (item N (h,[])) r'` by METIS_TAC [transImpValidItem] THEN
      METIS_TAC [shiftReduceGoto, parseInv, validStates_def]
      ) THEN
`?l. ~(l = []) /\ (stackSyms t ++ [q'] ++ l = pfx ++ h)`
    by METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL] THEN
`(?l1 l2.(l'=l1++l2) /\
(pfx=stackSyms t ++ [q']++l1) /\
(h=l2)) \/
(?h1 h2.(h=h1++h2) /\
(stackSyms t ++ [q'] = pfx++h1) /\
 (l'=h2)) \/
((stackSyms t ++ [q'] = pfx) /\ 
(l'=h))` by (SRW_TAC [] [] THEN
`?l1 l2.(pfx=stackSyms t ++[q'] ++l1) /\ (h=l2) /\
 (l'=l1++l2) \/
 (h=l2++[q']++l') /\ (pfx=l1) /\
 (stackSyms t = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [] [])
THENL[
      SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`N`,`h`,`stackSyms t++[q']++l1`,
			      `sfx`] THEN
      SRW_TAC [] []
      THENL[

	    METIS_TAC [APPEND_11, APPEND, APPEND_ASSOC],

	    `l1 ++ h ++ sfx = h'::h''::t''` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    SRW_TAC [] [] THEN
	    Cases_on `l1++h` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isPfxListSeq, APPEND, APPEND_ASSOC]
	    ],


      SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`N`, `h1++h2`, `pfx`, `sfx`] THEN
      SRW_TAC [] []
      THENL[
	    METIS_TAC [APPEND_11, APPEND, APPEND_ASSOC],


	    `h2++sfx = h'::h''::t''` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    Cases_on `h2` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [isPfxListSeq, APPEND, APPEND_ASSOC]
	    ],


      SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`N`, `h`, `stackSyms t ++ [q']`, `sfx`] THEN
      SRW_TAC [] []
      THENL[
	    METIS_TAC [APPEND_11, APPEND, APPEND_ASSOC],

	    `h++sfx=h'::h''::t''` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    Cases_on `h` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [isPfxListSeq, APPEND, APPEND_ASSOC]
	    ]
      ]])


val vsiImpvi = store_thm
("vsiImpvi",
``!l1 e.validStlItemsStack (l1:(((symbol#state)#ptree)list)) [(sym,st)] ==>
  validStlItems l1 st``,
Induct_on `l1` THEN SRW_TAC [] [validStlItemsStack_def])


val vpPropValidItemThmStlNil = store_thm 
("vpPropValidItemThmStlNil",
``!m g.(auggr g st eof = SOME ag) ==>
(slr ag = SOME m) ==> 
(stl=[]) ==>
RTC (rderives ag) [NTS (startSym ag)] ((stackSyms stl)++ininp) ==>
RTC (rderives ag) ((stackSyms stl)++ininp) (onstk++ininp) ==>
EVERY isTmnlSym (onstk++ininp) ==>
(onstk = stacktreeleaves (REVERSE stl)) ==>
(sl=onstk++ininp) ==>
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
validItemInv (ag, stl, csl) ==>
parseInv (ag, stl, csl) ==>
viablePfx ag (N,h) (stackSyms stl++ininp) (stackSyms stl) ==>
((parse (SOME m) (ininp, stl, csl) = SOME (sl',stl',csl'))) ==>
?N' h'.viablePfx ag (N',h') (stackSyms stl'++sl') 
       (stackSyms stl')``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
Cases_on `ininp` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.ABBREV_TAC `init = initItems ag (rules ag)` THEN
Cases_on `t` THEN Cases_on `getState m init h'` THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[

  Q.PAT_ASSUM `doReduce X Y Z = SOME Q` MP_TAC THEN 
  ASM_SIMP_TAC (srw_ss()) [doReduce_def, SYM sym_r1b, LET_THM] THEN
  Cases_on `addRule ([]:((symbol#state)#ptree)list) r` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN 
  Cases_on `r` THEN 
  FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def] THEN
  `MEM (item s (l,[])) init` by METIS_TAC [getState_mem_itl, parseInv, validStates_def, sgoto_exp] THEN
  `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
  SRW_TAC [] [pop_def] THEN
  FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def] THEN
  `stackSyms ([]:((symbol#state)#ptree)list) = 
          ([]:symbol list)` by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
  Q.ABBREV_TAC `inis = ([]:((symbol#state)#ptree)list)` THEN
  `pfx ++ h = stackSyms inis`
     by (SPOSE_NOT_THEN ASSUME_TAC THEN 
	 `?l. ~(l = []) /\ (stackSyms inis ++ l = pfx ++ h)`
            by METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL] THEN
`(?l1 l2.(l=l1++l2) /\
(pfx=stackSyms inis ++l1) /\
(h=l2)) \/
(?h1 h2.(h=h1++h2) /\
(stackSyms inis = pfx++h1) /\
 (l=h2)) \/
((stackSyms inis = pfx) /\ 
(l=h))` by METIS_TAC [twoListAppEq] THEN
SRW_TAC [] []
THENL[
      SRW_TAC [] []THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv] THEN
      `validStlItems inis init` by METIS_TAC [parseInv, SND, HD, itemlist_def,vsiImpvi] THEN
      `validStlItems inis [item s ([],[])]` by METIS_TAC [rgr_r9eq, validStlItems_append, getState_mem_itl, sgoto_exp, parseInv, validStates_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
      Cases_on `l1` THEN
      Cases_on `h` THEN
      Cases_on `sfx` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `N=startSym ag` THEN
      SRW_TAC [] [] 
      THENL[
	    METIS_TAC [MEM, MEM_APPEND, auggrStartRule],

	    `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
	    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

	    `[h']=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

	    `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
	    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
	    ],


      SRW_TAC [] [] THEN
      `h2++sfx=[h']` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      `(pfx=[]) /\ (h1=[])` by FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `MEM (item N ([],h2)) init` by METIS_TAC [initItemsHdNt] THEN
      Cases_on `h2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `N=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    `[h]=[NTS (startSym g);TS eof]`
		by METIS_TAC [auggrStartRule] THEN
	    FULL_SIMP_TAC (srw_ss()) [],
	    
	    METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND]
	    ],


      SRW_TAC [] [] THEN
      UNABBREV_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
      `MEM (item N ([],h)) (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt, APPEND_NIL] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `N=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    `[h']=[NTS (startSym g);TS eof]`
		by METIS_TAC [auggrStartRule] THEN
	    FULL_SIMP_TAC (srw_ss()) [],
	    
	    METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND]
	    ]
      ]) THEN
  UNABBREV_ALL_TAC  THEN
  FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
  SRW_TAC [] [] THEN
  `([NTS (startSym ag)] = [NTS N;h']) \/
   ?u.RTC (rderives ag) [NTS (startSym ag)] u 
   /\ rderives ag u [NTS N;h']` by METIS_TAC [RTC_CASES2]  THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, rderives_def] THEN
  SRW_TAC [][] THEN
  `(TS s') IN (followSet ag (NTS s))` by METIS_TAC [sgoto_exp, getState_reduce_followSet,validStates_def, parseInv, isTmnlSym_def] THEN  
  `(TS s') IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
  `MEM (item N ([],[])) (initItems ag (rules ag))`
      by METIS_TAC [initItemsHdNt] THEN
  `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
      by METIS_TAC [trans_def] THEN
  `(item s ([],[]) =item N ([],[])) ` by METIS_TAC [slrCompItemsEq, completeItem_def, itemLhs_def, isTmnlSym_def] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [] []THEN
  MAP_EVERY Q.EXISTS_TAC [`lhs`, `rhs`,`s1`, `s2`] THEN
  SRW_TAC [] [] THEN
  Cases_on `s1` THEN Cases_on `rhs` THEN
  SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, IS_PREFIX],

(* doRed - multiple ininp *)
  
  Q.PAT_ASSUM `doReduce X Y Z = SOME Q` MP_TAC THEN 
  ASM_SIMP_TAC (srw_ss()) [doReduce_def, SYM sym_r1b, LET_THM] THEN
  Cases_on `addRule ([]:((symbol#state)#ptree)list) r` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN 
  Cases_on `r` THEN 
  FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def] THEN
  `MEM (item s (l,[])) init` by METIS_TAC [getState_mem_itl, parseInv, validStates_def, sgoto_exp] THEN
  `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
  SRW_TAC [] [pop_def] THEN
  FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def] THEN
  `stackSyms ([]:((symbol#state)#ptree)list) = 
          ([]:symbol list)` by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
  FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
  SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [stacktreeleaves_def] THEN
  Cases_on `pfx` THEN
  Cases_on `h` THEN
  Cases_on `sfx` THEN
  SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [stacktreeleaves_def]
THENL[

      `MEM (item N ([],[])) init` by METIS_TAC [initItemsHdNt] THEN
      `h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, parseInv, validStates_def, sgoto_exp] THEN
      `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
      by METIS_TAC [trans_def] THEN
      `item N ([],[]) = item s ([],[])` by METIS_TAC [slrCompItemsEq, itemLhs_def, completeItem_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `([NTS (startSym ag)] =
            (NTS N::h::h''::t')) \/
       ?u.RTC (rderives ag) [NTS (startSym ag)] u /\
          rderives ag u (NTS N::h::h''::t')`
      by METIS_TAC [RTC_CASES2] THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`lhs`, `rhs`, `s1`, `s2`] THEN
      SRW_TAC [] [] THEN
      Cases_on `s1` THEN Cases_on `rhs` THEN
      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX, isTmnlSym_def],

      
      `N=startSym ag` by METIS_TAC [auggrRtcRderivesSt] THEN
      SRW_TAC [] [] THEN
      `h'::h''::t' = [NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      
      `MEM (item N ([],h'::t)) init` by METIS_TAC [initItemsHdNt] THEN
      `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, parseInv, validStates_def, sgoto_exp] THEN
      `validItl ag [item s ([],[])]` 
	  by METIS_TAC [parseInv, rgr_r9eq, validStates_def, validItl_append, validItl_def] THEN
      `validItl ag [item N ([],h'::t)]` 
	  by METIS_TAC [parseInv, rgr_r9eq, validStates_def, validItl_append, validItl_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
      by METIS_TAC [trans_def] THEN
      METIS_TAC [slrNotValid, sgoto_exp, APPEND],

      Cases_on `N=startSym ag` THEN
      SRW_TAC [] [] 
      THENL[
	    METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

	    `RTC (rderives ag) [NTS (startSym ag)]
             ((h'::h''::t') ++ [NTS N])` by FULL_SIMP_TAC (srw_ss()) []	THEN
	    `?p.[]=p++[TS eof]` by METIS_TAC [APPEND_NIL, lastEof] THEN
	    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
	    ],


      
      `RTC (rderives ag) [NTS (startSym ag)]
			   ((h'::t) ++ [NTS N] ++ (h::t''))` 
	  by FULL_SIMP_TAC (srw_ss()) [] THEN
      `?lhs rst.MEM (item lhs ([],h'::rst)) init` by METIS_TAC [initItemsNtInBtwn,HD, NOT_CONS_NIL, EVERY_DEF, EVERY_APPEND] THEN
      `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, parseInv, validStates_def, sgoto_exp] THEN
      `validItl ag [item s ([],[])]` 
	  by METIS_TAC [parseInv, rgr_r9eq, validStates_def, validItl_append, validItl_def] THEN
      `validItl ag [item lhs ([],h'::rst)]` 
	  by METIS_TAC [parseInv, rgr_r9eq, validStates_def, validItl_append, validItl_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
      by METIS_TAC [trans_def] THEN
      METIS_TAC [slrNotValid, sgoto_exp, APPEND],

      Cases_on `N=startSym ag` THEN
      SRW_TAC [] [] 
      THENL[
	    `h''''::t'' = [NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
	    SRW_TAC [] [] THEN
	    `EVERY isTmnlSym (t++[NTS (startSym g); TS eof])`
		by METIS_TAC [EVERY_DEF, isTmnlSym_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

	    `RTC (rderives ag) [NTS (startSym ag)]
             ((h'::t) ++ [NTS N])` by FULL_SIMP_TAC (srw_ss()) [] THEN
	    `?p.[]=p++[TS eof]` by METIS_TAC [APPEND_NIL, lastEof] THEN
	    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
	    ],

      Cases_on `N=startSym ag` THEN
      SRW_TAC [] [] 
      THENL[
	    `h''''::t'' = [NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
	    SRW_TAC [] [] THEN
	    `EVERY isTmnlSym (t++[NTS (startSym g); TS eof]++h::t''')`
		by METIS_TAC [EVERY_DEF, isTmnlSym_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],



      `RTC (rderives ag) [NTS (startSym ag)]
			   ((h'::t) ++ [NTS N] ++ (h::t'''))` 
	  by FULL_SIMP_TAC (srw_ss()) [] THEN
      `?lhs rst.MEM (item lhs ([],h'::rst)) init` by METIS_TAC [initItemsNtInBtwn,HD, NOT_CONS_NIL, EVERY_DEF, EVERY_APPEND] THEN
      `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, parseInv, validStates_def, sgoto_exp] THEN
      `validItl ag [item s ([],[])]` 
	  by METIS_TAC [parseInv, rgr_r9eq, validStates_def, validItl_append, validItl_def] THEN
      `validItl ag [item lhs ([],h'::rst)]` 
	  by METIS_TAC [parseInv, rgr_r9eq, validStates_def, validItl_append, validItl_def] THEN
      FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
      by METIS_TAC [trans_def] THEN
      METIS_TAC [slrNotValid, sgoto_exp, APPEND]
      ]],


      (* GOTO l *)
      SRW_TAC [] [push_def] THEN
      FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def] THEN
      `stackSyms ([]:((symbol#state)#ptree)list) = 
          ([]:symbol list)` by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [stacktreeleaves_def] THEN
      Cases_on `pfx` THEN
      Cases_on `h` THEN
      Cases_on `sfx` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[
      
	    `MEM (item N ([],[])) (initItems ag (rules ag))` 
	    by METIS_TAC [initItemsHdNt] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
	    `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
		by METIS_TAC [trans_def] THEN
	    METIS_TAC [shiftReduceGoto, validStates_def, parseInv],


	    `N = startSym ag` by METIS_TAC [auggrRtcRderivesSt] THEN
	    `(h'::h''::t') = [NTS (startSym g); TS eof]`
	    by METIS_TAC [auggrStartRule] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
	    
	    MAP_EVERY Q.EXISTS_TAC [`N`, `h'::t`, `[]`, `h::t''`] THEN
	    SRW_TAC [] [IS_PREFIX],
      
      
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],


		  `RTC (rderives ag) [NTS (startSym ag)]
                       ((h'::h''::t') ++ [NTS N])` by FULL_SIMP_TAC (srw_ss()) [] THEN
		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],


	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

		  MAP_EVERY Q.EXISTS_TAC [`N`, `[]`,`h'::t`, `h::t''`] THEN
		  SRW_TAC [] [IS_PREFIX]
		  ],

	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  `h''''::t'' = [NTS (startSym g); TS eof]`
		      by METIS_TAC [auggrStartRule] THEN
		  `EVERY isTmnlSym (h''''::t'')`
		      by METIS_TAC [EVERY_DEF, EVERY_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
		  SRW_TAC [] [],


		  `RTC (rderives ag) [NTS (startSym ag)]
                       ((h'::t) ++ [NTS N])` by FULL_SIMP_TAC (srw_ss()) [] THEN
		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],
	    
	    MAP_EVERY Q.EXISTS_TAC [`N`, `h''''::t''`, `h'::t`, 
				    `h::t'''`] THEN
	    SRW_TAC [] [IS_PREFIX]
	    ]])

val _ = export_theory();