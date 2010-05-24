open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
yaccDefTheory parseProp1DefTheory parseProp2DefTheory
lrGrammarDefTheory validItemInvTheory macStepTheory complDefTheory


val _ = Globals.linewidth := 60

val _ = set_trace "Unicode" 1

val isUnambiguous0 = 
Define
`isUnambiguous0 g = 
     ∀sl.sl ∈ language g 
            ==>
     (∀dl dl'. (rderives g ⊢ dl ◁ [NTS (startSym g)] → sl ∧
     rderives g ⊢ dl' ◁ [NTS (startSym g)] → sl) 
        ⇒
     (dl=dl'))`



val listDiffPfxSame = store_thm
("listDiffPfxSame" ,
``∀l l'.¬(l=l') ==>
(LENGTH l > LENGTH l' /\ ?sfx.l=l'++sfx) ∨
(LENGTH l' > LENGTH l /\ ?sfx.l'=l++sfx) ∨
(∃pfx h sfx h' sfx'.
 (l=pfx++[h]++sfx) /\
 (l'=pfx++[h']++sfx') /\ 
 ¬(h=h'))``,
Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) []
THENL[
      METIS_TAC [APPEND_NIL,APPEND],

      RES_TAC 
      THENL[
	    Cases_on `h=h'` THEN
	    SRW_TAC [][] 
            THENL[
		  Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  DISJ1_TAC THEN
		  DECIDE_TAC,

		  METIS_TAC [APPEND_NIL,APPEND]
		  ],

	    Cases_on `h=h'` THEN
	    SRW_TAC [][] 
	    THENL[
		  DISJ2_TAC THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN	    
		  FULL_SIMP_TAC (arith_ss) [],
		  
		  METIS_TAC [APPEND_NIL,APPEND]
		  ],

	    Cases_on `h=h'` THEN
	    SRW_TAC [][] 
	    THENL[
		  DISJ2_TAC THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN	    
		  FULL_SIMP_TAC (arith_ss) [],
		  
		  METIS_TAC [APPEND_NIL,APPEND]
		  ] THEN
	    METIS_TAC [APPEND_NIL,APPEND]
      ]])


val snoc_exists = store_thm
("snoc_exists",
``∀l.¬(l=[]) ==> ∃l'.((SNOC (LAST l) l') = l)``,
HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [][] THEN
Cases_on `l=[]`THEN FULL_SIMP_TAC (srw_ss())[]THEN
SRW_TAC [][] 
THENL[
      Q.EXISTS_TAC `[]` THEN
      SRW_TAC [][SNOC],
      FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND] THEN	    
      Q.EXISTS_TAC `l` THEN
      SRW_TAC [][] THEN	    
      METIS_TAC [last_append,NOT_CONS_NIL,APPEND,LAST_CONS]
      ])

val listDiffSfxSame = store_thm
("listDiffSfxSame" ,
``∀l l'.¬(l=l') ==>
(LENGTH l > LENGTH l' /\ ?pfx.l=pfx++l') ∨
(LENGTH l' > LENGTH l /\ ?pfx.l'=pfx++l) ∨
(∃pfx h pfx' h' sfx.
 (l=pfx++[h]++sfx) /\
 (l'=pfx'++[h']++sfx) /\ 
 ¬(h=h'))``,
HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [] [] 
THENL[
      Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) [],

 
      Cases_on `l'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND] THEN
	    DECIDE_TAC,

	    `∃l''. l'=SNOC (LAST l') l''` 
		by METIS_TAC [snoc_exists] THEN
	    FULL_SIMP_TAC (srw_ss()) []  THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND] THEN
	    Q.ABBREV_TAC `x'=LAST l'` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `l=l''` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (arith_ss) []
	    THENL[
		  METIS_TAC [APPEND_NIL],

		  RES_TAC THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  FULL_SIMP_TAC (arith_ss) [] 
		  THENL[
			Cases_on `x=x'` THEN
			SRW_TAC [][] THEN
			METIS_TAC [APPEND_NIL],

			Cases_on `x=x'` THEN
			SRW_TAC [][] THEN
			METIS_TAC [APPEND_NIL],

			Cases_on `x=x'` THEN
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			METIS_TAC [APPEND_NIL,APPEND_ASSOC]
			]]]])


val memLast = store_thm 
("memLast",
``∀l.¬(l=[]) ==> MEM (LAST l) l``,
Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [])



val ntList = store_thm
("ntList",
``!s1 s2 n n' s1' s2'.
(s1++[NTS n]++s2=s1'++[NTS n']++s2') ==>
EVERY isTmnlSym (s2++s2') ==>
(s1=s1') /\ (n=n') /\ (s2=s2')``,
SRW_TAC [][] THEN
`(s1' = s1++[NTS n]) ∨
         (∃pfx sfx.
            (s1++[NTS n] = s1' ++ [NTS n'] ++ pfx) ∧
            (s2' = pfx ++ sfx)) ∨
         ∃pfx sfx. (s1' = pfx ++ sfx) ∧ (s1++[NTS n] = pfx)`
    by METIS_TAC [listCompLens,APPEND_ASSOC] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      `s2=[NTS n']++s2'` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      Cases_on `pfx=[]`  THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    METIS_TAC [lastElemEq,APPEND_11],
	    `LAST [NTS n] = LAST pfx`
		by METIS_TAC [last_append,APPEND_ASSOC,MEM,MEM_APPEND] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `EVERY isTmnlSym (FRONT pfx ++ [NTS n])` by METIS_TAC [APPEND_FRONT_LAST] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
	    ],

      `s2=sfx++[NTS n']++s2'` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      `s2=[NTS n']++s2'` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      Cases_on `pfx=[]`  THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    METIS_TAC [lastElemEq,APPEND_11,symbol_11],
	    `LAST [NTS n] = LAST pfx`
		by METIS_TAC [last_append,APPEND_ASSOC,MEM,MEM_APPEND] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `EVERY isTmnlSym (FRONT pfx ++ [NTS n])` by METIS_TAC [APPEND_FRONT_LAST] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
	    ],

      `s2=sfx++[NTS n']++s2'` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],      

      `s2=[NTS n']++s2'` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      
      Cases_on `pfx=[]`  THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) []  THEN
      `LAST [NTS n] = LAST pfx`
	  by METIS_TAC [last_append,APPEND_ASSOC,MEM,MEM_APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `EVERY isTmnlSym (FRONT pfx ++ [NTS n])` by METIS_TAC [APPEND_FRONT_LAST] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      `s2=sfx++[NTS n']++s2'` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
      ])


val rtc2listRd = store_thm 
("rtc2listRd",
``!pfx sfx h h'.
rtc2list R (pfx++[h]++[h']++sfx) ==>
R h h'``,
Induct_on `pfx` THEN SRW_TAC [][] THEN
METIS_TAC [rtc2list_distrib_append_snd,MEM,MEM_APPEND,APPEND])

val rtc2listSt = store_thm
("rtc2listSt",
``∀dl.(auggr g st eof = SOME ag) ==>
 rsf ag (HD dl) ==>
 rtc2list (rderives ag) dl ==>
 ∀e.MEM e (TL dl) ==>  
   ¬(e=[NTS (startSym ag)])``,

Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`rsf ag h'` by METIS_TAC [rsf_def,RTC_RULES_RIGHT1] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
SRW_TAC [][] THEN
Cases_on `lhs=startSym ag` 
THENL[
      SRW_TAC [][] THEN
      `(s1=[]) /\ (s2=[])`by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [auggrStNotInRhs,APPEND_NIL],

      `?p.s2=p++[TS eof]` by METIS_TAC [lastEof] THEN
      SRW_TAC [][] THEN
      `LENGTH (s1 ++ rhs ++ p ++ [TS eof]) = 
        LENGTH [NTS (startSym ag)]`
      by METIS_TAC [APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `s1` THEN Cases_on `rhs` THEN
      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
      ])
      
val slrmacConf1 = store_thm
("slrmacConf1",
``(slrmac ag = SOME m) ==>
  (auggr g st eof = SOME ag) ==>
  MEM (rule lhs rhs) (rules ag) ==>
  MEM (rule lhs' rhs') (rules ag) ==>
  rsf ag (s1 ++ [NTS lhs] ++ s) ==>
  rsf ag (s1' ++ [NTS lhs'] ++ p ++ s) ==>
  EVERY isTmnlSym (p ++ s) ==>
 (s1 ++ rhs = s1' ++ rhs' ++ p) ==>
 (s1 ++ [NTS lhs] = s1' ++ [NTS lhs'] ++ p)``,

SRW_TAC [][] THEN
`(s1 = s1'++rhs') ∧ (rhs = p) ∨
 (∃px sx.
     (s1 = s1' ++ rhs'++ px) ∧ (rhs = sx) ∧
     (p = px ++ sx)) ∨
 ∃px sx.
 (s1'++rhs' = s1 ++ px) ∧ (p = sx) ∧ (rhs = px++sx)`
    by METIS_TAC [twoListAppEq] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
      `?n.NRC (rderives ag) n 
        [NTS (startSym ag)]
	(s1' ++ rhs' ++ [NTS lhs] ++ s)`
      by METIS_TAC [RTC_NRC] THEN
      `?s.(trans ag (initItems ag (rules ag),s1' ++ rhs') =
          SOME s) /\ MEM (item lhs ([],p)) s` 
	  by METIS_TAC [lemma] THEN
      `validItem ag (s1'++rhs') (item lhs' (rhs',[]))`
      by (SRW_TAC [] [validItem_def] THEN
	  Q.EXISTS_TAC `p++s` THEN
	  SRW_TAC [][] THEN
	  METIS_TAC [rderives_append,rdres1,EVERY_APPEND,APPEND_ASSOC]) THEN
      `MEM (item lhs' (rhs',[])) s'` 
	  by METIS_TAC [transImpValidItem] THEN
      Cases_on `lhs=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    `p=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
	    SRW_TAC [][] THEN
	    `(s1'++rhs'=[]) /\ (s=[])`
	    by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
	    
	    `?h t.p++s=h::t` by METIS_TAC [list_nchotomy,MEM,MEM_APPEND,lastEof] THEN
	    SRW_TAC [][] THEN
	    `h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
	    Cases_on `p` THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    THENL[
		  SRW_TAC [][] THEN
		  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		  `(item lhs' (rhs',[])=(item lhs ([],[])))` 
		      by METIS_TAC [transImpValidItem,completeItem_def,
				    itemLhs_def,slrmacCompItemsEq] THEN
		  FULL_SIMP_TAC (srw_ss()) [],

		  SRW_TAC [][] THEN
		  METIS_TAC [slrmacNotValid,sgoto_exp]
		  ]
	    ],


      FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
      SRW_TAC [][] THEN
      `?n.NRC (rderives ag) n [NTS (startSym ag)]
            (s1' ++ rhs' ++ px ++ [NTS lhs] ++ s)`
      by METIS_TAC [RTC_NRC] THEN
      `?s.(trans ag (initItems ag (rules ag),s1' ++ rhs'++px) =
          SOME s) /\ MEM (item lhs ([],rhs)) s` 
	  by METIS_TAC [lemma] THEN      
      `validItem ag (s1'++rhs') (item lhs' (rhs',[]))`
      by (SRW_TAC [][validItem_def] THEN
	  Q.EXISTS_TAC `px++rhs++s` THEN SRW_TAC [][] THEN
	  METIS_TAC [rdres1,rderives_append,EVERY_APPEND,APPEND_ASSOC]) THEN
      `?s''.(trans ag (initItems ag (rules ag),s1' ++ rhs') =
	     SOME s'') /\ (trans ag (s'',px) = SOME s')` 
	  by METIS_TAC [transAppend] THEN          
      `MEM (item lhs' (rhs',[])) s''`
      by METIS_TAC [transImpValidItem] THEN
      Cases_on `lhs=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    `rhs=[NTS (startSym g); TS eof]`
		by METIS_TAC [auggrStartRule] THEN
	    SRW_TAC [][] THEN
	    `(s1'++rhs'++px=[]) /\ (s=[])`
		by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

	    `¬(s=[])` by METIS_TAC [lastEof,MEM,MEM_APPEND] THEN
	    `¬(px++rhs++s = [])` by SRW_TAC [][] THEN
	    Cases_on `px` THEN SRW_TAC [][]
            THENL[
		  FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
		  Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] 
		  THENL[
			`h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN			
			METIS_TAC [slrmacNotValid,sgoto_exp,EVERY_DEF],

			Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			`h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
			`h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
			`(item lhs' (rhs',[])=(item lhs ([],[])))` 
			    by METIS_TAC [transImpValidItem,completeItem_def,
					  itemLhs_def,slrmacCompItemsEq] THEN
			FULL_SIMP_TAC (srw_ss()) [],
			
			`h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
			METIS_TAC [slrmacNotValid,sgoto_exp,EVERY_DEF]
			],		  
		  
		  FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
		  Cases_on `moveDot s'' h` THEN 
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `∃l r1 r2.
                     (h' = item l (r1 ++ [h],r2)) ∧
                     MEM (item l (r1,h::r2)) s''`
		      by METIS_TAC [mdMem,MEM] THEN
		  `h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
		  METIS_TAC [slrmacNotValid,sgoto_exp,EVERY_DEF]		  
		  ]
	    ],

      
      FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
      SRW_TAC [][] THEN
      `∃n.NRC (rderives ag) n [NTS (startSym ag)]
            (s1 ++ [NTS lhs] ++ s)` 
      by METIS_TAC [RTC_NRC] THEN
      `∃s.(trans ag (initItems ag (rules ag),s1) = SOME s) /\
          MEM (item lhs ([],px ++ p)) s`
      by METIS_TAC [lemma] THEN
      Cases_on `lhs=startSym ag`  THEN SRW_TAC [][]
      THENL[
	    `px++p=[NTS (startSym g);TS eof]`
	    by METIS_TAC [auggrStartRule] THEN
	    `(s1=[]) /\ (s=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `lhs'=startSym ag` THEN
	    SRW_TAC [][]
	    THENL[
		  METIS_TAC [auggrRtcRderivesPfxSfxNil,APPEND_NIL],

		  FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
		  Cases_on `s1'` THEN
		  Cases_on `rhs'` THEN
		  Cases_on `p` THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
                  THENL[
			SRW_TAC [][] THEN
			METIS_TAC [APPEND,APPEND_NIL,auggrEofInRhs,MEM,MEM_APPEND],

			SRW_TAC [][] THEN
			Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			SRW_TAC [][] THEN
			`MEM (item lhs' ([],[NTS (startSym g)]))
		          (initItems ag (rules ag))`
			by METIS_TAC [initItemsHdNt,APPEND] THEN
			`TS eof ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
			`∃s.(trans ag (initItems ag (rules ag),[NTS (startSym g)])
			   = SOME s) /\ 
                          MEM (item lhs' ([NTS (startSym g)],[])) s /\
                          MEM (item (startSym ag) ([NTS (startSym g)],[TS eof])) s` 
			    by (SRW_TAC [][trans_def] THEN
			Cases_on `moveDot (initItems ag (rules ag)) (NTS (startSym g))` THEN
			SRW_TAC [][] THEN
			METIS_TAC [mdMemExists,APPEND,APPEND_NIL,MEM,iclosure_mem]) THEN
			METIS_TAC [isTmnlSym_def,sgoto_exp,slrmacNotValid],

			SRW_TAC [][] THEN
			`[NTS (startSym g); TS eof; NTS lhs']=
           		  [NTS (startSym g); TS eof]++ [NTS lhs']`
			    by SRW_TAC [][] THEN
			METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND],


			Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			SRW_TAC [][] THEN
			`[NTS (startSym g); NTS lhs'; TS eof]=
                           [NTS (startSym g)]++ [NTS lhs']++[TS eof]`
			    by SRW_TAC [][] THEN
			`∃s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) = SOME s)
                          /\ MEM (item lhs' ([],[])) s`
			    by METIS_TAC [lemma,RTC_NRC] THEN
			`validItem ag [NTS (startSym g)] (item (startSym ag) ([NTS (startSym g)], [TS eof]))`
			    by (SRW_TAC [] [validItem_def] THEN
				MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1]) THEN
			`TS eof ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
			METIS_TAC [slrmacNotValid,isTmnlSym_def,APPEND,sgoto_exp,transImpValidItem],

			Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			SRW_TAC [][]THEN
			METIS_TAC [auggrEofInRhs,APPEND_NIL],

			Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
			]
		  ],

	    `¬(s=[])` by METIS_TAC [lastEof,MEM,MEM_APPEND] THEN
	    Cases_on `s` THEN SRW_TAC [][] THEN
	    `h ∈ (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						
	    IMP_RES_TAC twoListAppEq THEN
	    SRW_TAC [][]
	    THENL[
		  `validItem ag s1 (item lhs' ([],px))`
		      by (SRW_TAC [] [validItem_def] THEN
			  Q.EXISTS_TAC `p++h::t` THEN
			  SRW_TAC [][] THEN
			  METIS_TAC [rdres1,EVERY_APPEND,
				     rderives_append,APPEND,
				     EVERY_DEF,APPEND_ASSOC]) THEN
		  `MEM (item lhs' ([],px)) s'` by METIS_TAC [transImpValidItem] THEN
		  Cases_on `px` THEN
		  Cases_on `p` THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  THENL[

			`h ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN									
			METIS_TAC [transImpValidItem,completeItem_def,
				   itemLhs_def,slrmacCompItemsEq],

			`h' ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
			METIS_TAC [slrmacNotValid,sgoto_exp],

			`h ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN									
			`∃s''. trans ag (s',h'::t') = SOME s''`
			    by METIS_TAC [ruleRhsExistsImpTrans] THEN
			`validItem ag (s1++h'::t') (item lhs' (h'::t',[]))`
			    by (SRW_TAC [] [validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1,EVERY_APPEND,
					   rderives_append,APPEND,
					   EVERY_DEF,APPEND_ASSOC]) THEN
			`validItem ag (s1++h'::t') (item lhs (h'::t',[]))`
			    by (SRW_TAC [] [validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1,EVERY_APPEND,
					   rderives_append,APPEND,
					   EVERY_DEF,APPEND_ASSOC]) THEN
			`trans ag (initItems ag (rules ag),s1++h'::t') = SOME s''`
			    by METIS_TAC [transSeq,initItems_def] THEN
			METIS_TAC [transImpValidItem,completeItem_def,
				   itemLhs_def,slrmacCompItemsEq],

			`∃s''. trans ag (s',h'::t') = SOME s''`
			    by METIS_TAC [ruleRhsExistsImpTrans] THEN
			`validItem ag (s1++h'::t') (item lhs' (h'::t',[]))`
			    by (SRW_TAC [] [validItem_def] THEN
				Q.EXISTS_TAC `h''::t''++h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1,EVERY_APPEND,
					   rderives_append,APPEND,
					   EVERY_DEF,APPEND_ASSOC]) THEN
			`validItem ag (s1++h'::t') (item lhs (h'::t',h''::t''))`
			    by (SRW_TAC [] [validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				`(s1 ++ h'::t' ++ h''::t'' ++ h::t) 
                                  = s1 ++ (h'::(t' ++ h''::t'')) ++ h::t`
				    by METIS_TAC [APPEND_ASSOC,APPEND] THEN
				METIS_TAC [rdres1,rderives_append,EVERY_DEF]) THEN
			`trans ag (initItems ag (rules ag),s1++h'::t') = SOME s''`
			    by METIS_TAC [transSeq,initItems_def] THEN
			`h'' ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN									
			METIS_TAC [slrmacNotValid,sgoto_exp, transImpValidItem]
			],


		  Cases_on `p` THEN SRW_TAC [][] THEN
		  Cases_on `s1''` THEN SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  THENL[
			`∃s.(trans ag (initItems ag (rules ag),s1) = SOME s)
                          /\ MEM (item lhs ([],rhs')) s`
			by METIS_TAC [lemma] THEN
			`MEM (item lhs' ([],rhs')) s`
			    by METIS_TAC [lemma,transOutEq,RTC_NRC] THEN
			IMP_RES_TAC ruleRhsExistsImpTrans THEN
			`h ∈ (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
			`validItem ag (s1++rhs') (item lhs (rhs',[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1,EVERY_DEF,rderives_append]) THEN
			`validItem ag (s1++rhs') (item lhs' (rhs',[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1,EVERY_DEF,rderives_append]) THEN
			`(∃s'. (trans ag (s,rhs') = SOME s')) /\ ∃s''. (trans ag (s',rhs') = SOME s'')`
			    by METIS_TAC [] THEN
			`s''=s'''` by METIS_TAC [transOutEq] THEN
			SRW_TAC [][] THEN
			`trans ag (initItems ag (rules ag),s1++rhs') = SOME s''` by METIS_TAC [transSeq,initItems_def] THEN
			METIS_TAC [slrmacCompItemsEq,itemLhs_def,completeItem_def,transImpValidItem],


			`∃s.(trans ag (initItems ag (rules ag),s1) = SOME s)
                          /\ MEM (item lhs ([],h'::(t'++rhs'))) s`
			by METIS_TAC [lemma] THEN
			`validItem ag (s1++h'::t'++rhs') (item lhs' (rhs',[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [rdres1,rderives_append,EVERY_DEF,APPEND_ASSOC]) THEN
			`validItem ag (s1++h'::t'++rhs') (item lhs (h'::(t'++rhs'),[]))`
			    by (SRW_TAC [][validItem_def] THEN
			        Q.EXISTS_TAC `s1` THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] 
				THENL[
				      METIS_TAC [rdres1,rderives_append,EVERY_DEF,APPEND_ASSOC],
				      METIS_TAC [APPEND,APPEND_ASSOC]]) THEN
			`∃s'. trans ag (s,h'::(t' ++ rhs')) = SOME s'`
			    by METIS_TAC [ruleRhsExistsImpTrans] THEN			
			`trans ag (initItems ag (rules ag),s1++h'::(t' ++ rhs')) = SOME s''`
			    by METIS_TAC [transSeq,initItems_def] THEN
			`h ∈ (followSet ag (NTS lhs'))` 
			    by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
			`h'::(t'++rhs') = h'::t'++rhs'`
			    by METIS_TAC [APPEND,APPEND_ASSOC] THEN
			`MEM (item lhs (h'::(t' ++ rhs'),[])) s''`
			    by METIS_TAC [transImpValidItem,APPEND_ASSOC] THEN
			`MEM (item lhs' (rhs',[])) s''` 
			    by METIS_TAC [transImpValidItem,APPEND_ASSOC]  THEN
			`(item lhs' (rhs',[]) = item lhs (h'::(t' ++ rhs'),[]))`
			    by METIS_TAC [slrmacCompItemsEq,itemLhs_def,completeItem_def,transImpValidItem] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			METIS_TAC [APPEND_11,APPEND,APPEND_ASSOC],

			`∃s.(trans ag (initItems ag (rules ag),s1) = SOME s)
                          /\ MEM (item lhs ([],rhs'++h'::t')) s`
			by METIS_TAC [lemma] THEN
			`∃s'. trans ag (s,rhs' ++ h'::t') = SOME s'`
			    by METIS_TAC [ruleRhsExistsImpTrans] THEN
			`trans ag (initItems ag (rules ag),s1++rhs'++h'::t') = SOME s''`
			by METIS_TAC [transSeq,initItems_def,APPEND_ASSOC] THEN
			`?s'''.trans ag (initItems ag (rules ag),s1++rhs') = SOME s'''`
			by METIS_TAC [transOverAppend] THEN
			`validItem ag (s1++rhs') (item lhs (rhs',h'::t'))`
			by (SRW_TAC [] [validItem_def] THEN
			    Q.EXISTS_TAC `h::t` THEN
			    SRW_TAC [] [] THEN
			    METIS_TAC [rdres1,rderives_append,EVERY_DEF,APPEND_ASSOC]) THEN
			`validItem ag (s1++rhs') (item lhs' (rhs',[]))`
			    by (SRW_TAC [] [validItem_def] THEN
			    Q.EXISTS_TAC `h'::t'++h::t` THEN
			    SRW_TAC [] [] THEN
			    METIS_TAC [rdres1,rderives_append,EVERY_DEF,APPEND_ASSOC,EVERY_APPEND]) THEN
			`h' ∈ (followSet ag (NTS lhs'))` 
			    by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN			
			METIS_TAC [slrmacNotValid,sgoto_exp,transImpValidItem],


			`∃s.(trans ag (initItems ag (rules ag),s1++h''::t'') = SOME s)
                          /\ MEM (item lhs' ([],rhs')) s`
			by METIS_TAC [lemma,RTC_NRC,APPEND_ASSOC] THEN
			`∃s'. trans ag (s,rhs') = SOME s'` 
			    by METIS_TAC [ruleRhsExistsImpTrans] THEN
			`trans ag (initItems ag (rules ag),s1 ++ h''::t''++rhs') 
		          = SOME s''` by METIS_TAC [transSeq,initItems_def] THEN
			`validItem ag (s1 ++ h''::t'' ++ rhs') (item lhs' (rhs',[]))`
			by (SRW_TAC [] [validItem_def] THEN
			    Q.EXISTS_TAC `h'::t'++h::t` THEN
			    SRW_TAC [][] THEN
			    `(s1 ++ h''::t'' ++ rhs' ++ h'::t' ++ h::t) =
              			(s1 ++ h''::t'') ++ rhs' ++ (h'::t' ++ h::t)`
				by METIS_TAC [APPEND_ASSOC] THEN
			    `EVERY isTmnlSym (h'::t' ++ h::t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
			    METIS_TAC [rdres1,rderives_append,APPEND_ASSOC]) THEN
			`validItem ag (s1 ++ h''::t'' ++ rhs') (item lhs ((h''::t'' ++ rhs'), h'::t'))`
			by (SRW_TAC [] [validItem_def] THEN
			    Q.EXISTS_TAC `h::t` THEN
			    SRW_TAC [][] THEN
			    `(s1 ++ h''::t'' ++ rhs' ++ h'::t' ++ h::t)=
                               (s1 ++ (h''::t'' ++ rhs' ++ h'::t') ++ h::t)`
				by METIS_TAC [APPEND_ASSOC] THEN
			    `h''::(t''++rhs'++h'::t') = h''::t''++rhs'++h'::t'`
				by SRW_TAC [][] THEN
			    METIS_TAC [rdres1,EVERY_DEF,rderives_append]) THEN
			`h' ∈ (followSet ag (NTS lhs'))` 
			    by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN			
			METIS_TAC [slrmacNotValid,sgoto_exp,transImpValidItem]
			],

		  Cases_on `s1''` THEN
		  SRW_TAC [][]
		  THENL[
			FULL_SIMP_TAC (srw_ss()) []THEN
			Cases_on `px` THEN
			Cases_on `p` THEN
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) []
			THENL[
			      `MEM (item lhs' ([],[])) s'`
			      by METIS_TAC [lemma,RTC_NRC,transOutEq] THEN
			      `h ∈ (followSet ag (NTS lhs'))` 
				  by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						      
			      METIS_TAC [slrmacCompItemsEq,itemLhs_def,completeItem_def],

			      `MEM (item lhs' ([],[])) s'`
			      by METIS_TAC [lemma,RTC_NRC,transOutEq,APPEND_ASSOC] THEN
			      `h' ∈ (followSet ag (NTS lhs'))` 
				  by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN						      
			      METIS_TAC [slrmacNotValid,sgoto_exp],

			      IMP_RES_TAC ruleRhsExistsImpTrans THEN
			      `∃s''. trans ag (s',h'::t') = SOME s''`
			      by METIS_TAC [] THEN
			      `trans ag (initItems ag (rules ag),s1'++h'::t') = SOME s''`
			      by METIS_TAC [transSeq,initItems_def] THEN
			      `validItem ag (s1'++h'::t') (item lhs (h'::t',[]))`
			      by (SRW_TAC [][validItem_def] THEN
				  Q.EXISTS_TAC `h::t` THEN
				  SRW_TAC [][] THEN
				  METIS_TAC [rdres1,rderives_append,EVERY_DEF]) THEN
			      `validItem ag (s1'++h'::t') (item lhs' (h'::t',[]))`
			      by (SRW_TAC [][validItem_def] THEN
				  Q.EXISTS_TAC `h::t` THEN
				  SRW_TAC [][] THEN
				  METIS_TAC [rdres1,rderives_append,EVERY_DEF]) THEN
			      `h ∈ (followSet ag (NTS lhs'))` 
				  by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN		
			      METIS_TAC [transImpValidItem,slrmacCompItemsEq,itemLhs_def,completeItem_def],


			      `∃s''.trans ag (s',h'::(t' ++ h''::t'')) = SOME s''`
			      by METIS_TAC [ruleRhsExistsImpTrans] THEN
			      `?s.trans ag (s',h'::t') = SOME s`
			      by METIS_TAC [APPEND,APPEND_ASSOC,transOverAppend] THEN
			      `trans ag (initItems ag (rules ag),s1'++h'::t') = SOME s`
				  by METIS_TAC [transSeq,initItems_def] THEN
			      `validItem ag (s1'++h'::t') (item lhs (h'::t',h''::t''))`
			      by (SRW_TAC [][validItem_def] THEN
				  Q.EXISTS_TAC `h::t` THEN
				  `(h'::(t' ++ h''::t'')=h'::t' ++ h''::t'')`
				      by METIS_TAC [APPEND_ASSOC,APPEND] THEN			
				  SRW_TAC [][]  THEN
				  METIS_TAC [rdres1,rderives_append,EVERY_DEF,APPEND_ASSOC]) THEN
			      `validItem ag (s1'++h'::t') (item lhs' (h'::t',[]))`
			      by (SRW_TAC [][validItem_def] THEN
				  Q.EXISTS_TAC `h''::t''++h::t` THEN
				  SRW_TAC [][] THEN
				  `EVERY isTmnlSym (h''::t'' ++ h::t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
				  METIS_TAC [rdres1,rderives_append,APPEND_ASSOC]) THEN
			      `h'' ∈ (followSet ag (NTS lhs'))` 
				  by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
			      METIS_TAC [slrmacNotValid,sgoto_exp,transImpValidItem]
			      ],
			
			`validItem ag (s1'++h'::t'++px) 
		           (item lhs (px,p))`
			by (SRW_TAC [] [validItem_def] THEN
			    Q.EXISTS_TAC `h::t` THEN
			    SRW_TAC [][] THEN
			    METIS_TAC [rderives_append,rdres1,
				       EVERY_DEF,APPEND_ASSOC]) THEN
			`validItem ag (s1'++h'::t'++px) 
			   (item lhs' (h'::t'++px,[])) `
			by (SRW_TAC [] [validItem_def] THEN
			    Q.EXISTS_TAC `p++h::t` THEN
			    `h'::t'++px=h'::(t'++px)`
				by SRW_TAC [][] THEN
			    METIS_TAC [rdres1,rderives_append,
				       EVERY_DEF,APPEND_ASSOC,
				       EVERY_APPEND]) THEN
			`∃s''. trans ag (s',px ++ p) = SOME s''` 
			    by METIS_TAC[ruleRhsExistsImpTrans] THEN
			`trans ag (initItems ag (rules ag),(s1' ++ h'::t') ++ (px++p)) = SOME s''`
			by METIS_TAC [transSeq,initItems_def] THEN
			`?sx.trans ag (initItems ag (rules ag),s1' ++ h'::t' ++ px ) =
		         SOME sx`
			by METIS_TAC [transOverAppend,APPEND_ASSOC] THEN
			Cases_on `p` THEN SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) []
			THENL[
			      `h ∈ (followSet ag (NTS lhs'))` 
				  by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN			      
			      `(item lhs' (h'::(t' ++ px),[])=(item lhs (px,[])))` 
				  by METIS_TAC [slrmacCompItemsEq,itemLhs_def,completeItem_def,transImpValidItem] THEN
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      SRW_TAC [][] THEN
			      METIS_TAC [APPEND_11,APPEND_ASSOC,NOT_CONS_NIL,APPEND],

			      `h'' ∈ (followSet ag (NTS lhs'))` 
				  by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC,rtcRdImpDg, 
					  isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN			      
			      METIS_TAC [transImpValidItem,slrmacNotValid,sgoto_exp]			      
			      ]
			]
		  ]]])



val slrmacConf = store_thm	
("slrmacConf",
``(slrmac ag = SOME m) ==>
  (auggr g st eof = SOME ag)==>
  MEM (rule lhs rhs) (rules ag) ==>
  MEM (rule lhs' rhs') (rules ag) ==>
  rsf ag (s1 ++ [NTS lhs] ++ s2) ==>
  rsf ag (s1' ++ [NTS lhs'] ++ s2') ==>
  EVERY isTmnlSym (s2++s2') ==>
  (s1 ++ rhs ++ s2 = s1' ++ rhs' ++ s2') ==>
  (s1 ++ [NTS lhs] ++ s2 = s1' ++ [NTS lhs'] ++ s2')``,

SRW_TAC [][] THEN
`(s1 ++ rhs) ++ s2 = (s1' ++ rhs') ++ s2'`
    by METIS_TAC [APPEND_ASSOC] THEN
`(s1++rhs = s1'++rhs') ∧ (s2 = s2') ∨
       (∃p s.
          (s1++rhs = (s1'++rhs') ++ p) ∧ (s2 = s) ∧
          (s2' = p ++ s)) ∨
       ∃p s.
         (s1'++rhs' = (s1++rhs) ++ p) ∧ (s2' = s) ∧ (s2 = p ++ s)`
    by METIS_TAC [twoListAppEq] THEN
SRW_TAC [][]
THENL[
      `(s1 = s1') ∧ (rhs = rhs') ∨
       (∃p s.
          (s1 = s1' ++ p) ∧ (rhs = s) ∧
          (rhs' = p ++ s)) ∨
       ∃p s.
         (s1' = s1 ++ p) ∧ (rhs' = s) ∧ (rhs = p++s)`
      by METIS_TAC [twoListAppEq] THEN
      SRW_TAC [][]
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
	    `?n.NRC (rderives ag) n 
              [NTS (startSym ag)]
              (s1 ++ [NTS lhs] ++ s2)`
	    by METIS_TAC [RTC_NRC] THEN
	    `?n.NRC (rderives ag) n 
              [NTS (startSym ag)]
              (s1 ++ [NTS lhs'] ++ s2)`
	    by METIS_TAC [RTC_NRC] THEN
	    IMP_RES_TAC lemma THEN
	    `(s=s') /\ (s=s'') /\ (s=s''')`
	    by METIS_TAC [transOutEq] THEN
	    SRW_TAC [][] THEN
	    Cases_on `lhs=startSym ag` THEN
	    SRW_TAC [][]
            THENL[
		  `rhs=[NTS (startSym g);TS eof]`
		      by METIS_TAC [auggrStartRule] THEN
		  METIS_TAC [auggrEofInRhs,APPEND,APPEND_NIL],
		  
		  `¬(s2=[])` by METIS_TAC [lastEof,MEM,MEM_APPEND] THEN
		  Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  `h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  IMP_RES_TAC ruleRhsExistsImpTrans THEN
		  `∃s'. trans ag (s,rhs) = SOME s'` by METIS_TAC [] THEN
		  `trans ag (initItems ag (rules ag),s1++rhs) = SOME s'`
		  by METIS_TAC [transSeq,initItems_def] THEN
		  `validItem ag (s1++rhs) (item lhs' (rhs,[]))`
		  by (SRW_TAC [][validItem_def] THEN
		      Q.EXISTS_TAC `h::t` THEN
		      SRW_TAC [][] THEN
		      METIS_TAC [EVERY_DEF,rdres1,rderives_append]) THEN
		  `validItem ag (s1++rhs) (item lhs (rhs,[]))`
		  by (SRW_TAC [][validItem_def] THEN
		      Q.EXISTS_TAC `h::t` THEN
		      SRW_TAC [][] THEN
		      METIS_TAC [EVERY_DEF,rdres1,rderives_append]) THEN
		  METIS_TAC [transImpValidItem,completeItem_def,itemLhs_def,slrmacCompItemsEq]
		  ],


	    FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
	    Cases_on `lhs=startSym ag` THEN
	    SRW_TAC [][]
	    THENL[
		  `rhs=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
		  SRW_TAC [][] THEN
		  `(p ++ [NTS (startSym g); TS eof] = 
                      (p++[NTS (startSym g)])++[TS eof]++[])`
		      by METIS_TAC [APPEND,APPEND_ASSOC,APPEND_NIL] THEN
		  `(p++[NTS (startSym g)]=[NTS (startSym g)]) /\ (lhs'=startSym ag)`
		      by METIS_TAC [auggrEofInRhs,APPEND_ASSOC] THEN		  
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

		  `¬(s2=[])` by METIS_TAC [lastEof,MEM,MEM_APPEND] THEN
		  Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  `h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  Cases_on `p=[]` THEN SRW_TAC [][]
                  THENL[
			FULL_SIMP_TAC (srw_ss()) []  THEN
			`?n.NRC (rderives ag) n [NTS (startSym ag)]
              		  (s1' ++ [NTS lhs] ++ h::t)`
			    by METIS_TAC [RTC_NRC] THEN
			IMP_RES_TAC lemma THEN
			IMP_RES_TAC ruleRhsExistsImpTrans THEN
			`∃s''. trans ag (s',rhs) = SOME s''` by METIS_TAC [] THEN
			`trans ag (initItems ag (rules ag),s1'++rhs) = SOME s''`
			    by METIS_TAC [transSeq,initItems_def] THEN
			`validItem ag (s1'++rhs) (item lhs (rhs,[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [EVERY_DEF,rdres1,rderives_append]) THEN
			`validItem ag (s1'++rhs) (item lhs' (rhs,[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [EVERY_DEF,rdres1,rderives_append]) THEN
			METIS_TAC [transImpValidItem,completeItem_def,itemLhs_def,slrmacCompItemsEq],

			`?n.NRC (rderives ag) n [NTS (startSym ag)]
              		  (s1' ++ p++ [NTS lhs] ++ h::t)`
			    by METIS_TAC [RTC_NRC] THEN
			IMP_RES_TAC lemma THEN
			IMP_RES_TAC ruleRhsExistsImpTrans THEN
			`∃s''. trans ag (s',rhs) = SOME s''` by METIS_TAC [] THEN
			`trans ag (initItems ag (rules ag),s1'++p++rhs) = SOME s''`
			    by METIS_TAC [transSeq,initItems_def] THEN
			`validItem ag (s1'++p++rhs) (item lhs (rhs,[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [EVERY_DEF,rdres1,rderives_append]) THEN
			`validItem ag (s1'++p++rhs) (item lhs' (p++rhs,[]))`
			    by (SRW_TAC [][validItem_def] THEN
				Q.EXISTS_TAC `h::t` THEN
				SRW_TAC [][] THEN
				METIS_TAC [EVERY_DEF,rdres1,rderives_append,APPEND_ASSOC]) THEN
			`?e t.p=e::t` by METIS_TAC [list_nchotomy] THEN
			SRW_TAC [][] THEN			
			`(item lhs' (e::t' ++ rhs,[])=(item lhs (rhs,[])))` 
				    by METIS_TAC [transImpValidItem,completeItem_def,itemLhs_def,slrmacCompItemsEq] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			METIS_TAC [APPEND,APPEND_11,NOT_CONS_NIL]
			]
		  ],
		  
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) []  THEN
	    FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
	    Cases_on `lhs=startSym ag` THEN
	    SRW_TAC [][]
            THENL[
		  `p++rhs'=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
		  Cases_on `p` THEN Cases_on `rhs'` THEN SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] 
		  THENL[
			      METIS_TAC [auggrEofInRhs,APPEND,APPEND_NIL],

			      `(s1=[]) /\ (s2=[])`
				  by METIS_TAC [auggrRtcRderivesPfxSfxNil,MEM,MEM_APPEND] THEN
			      SRW_TAC [][] THEN
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      Cases_on `lhs'=startSym ag` THEN
			      SRW_TAC [][] 
			      THENL[
				    `[NTS (startSym g); TS eof; NTS (startSym ag)] = [NTS (startSym g); TS eof]++ [NTS (startSym ag)]++[]`
					by METIS_TAC [APPEND,APPEND_NIL] THEN
				    METIS_TAC [auggrRtcRderivesPfxSfxNil,MEM,MEM_APPEND],
			      
				    `[NTS (startSym g); TS eof; NTS lhs']=[NTS (startSym g); TS eof]++ [NTS lhs']`
					by METIS_TAC [APPEND] THEN
				    METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND]
				    ],

			      Cases_on `t'` THEN Cases_on `t` THEN
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      SRW_TAC [][] THEN
			      METIS_TAC [APPEND_NIL,NOT_CONS_NIL,auggrEofInRhs]				    
			      ],
		  
		  `¬(s2=[])` by METIS_TAC [lastEof,MEM,MEM_APPEND] THEN
		  Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  `h IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  `?n.NRC (rderives ag) n [NTS (startSym ag)]
              		(s1 ++ p++ [NTS lhs'] ++ h::t)`
		      by METIS_TAC [RTC_NRC] THEN
		  IMP_RES_TAC lemma THEN
		  IMP_RES_TAC ruleRhsExistsImpTrans THEN
		  `∃s''. trans ag (s',rhs') = SOME s''` by METIS_TAC [] THEN
		  `trans ag (initItems ag (rules ag),s1++p++rhs') = SOME s''`
		      by METIS_TAC [transSeq,initItems_def] THEN
		  `validItem ag (s1++p++rhs') (item lhs' (rhs',[]))`
		      by (SRW_TAC [][validItem_def] THEN
			  Q.EXISTS_TAC `h::t` THEN
			  SRW_TAC [][] THEN
			  METIS_TAC [EVERY_DEF,rdres1,rderives_append]) THEN
		  `validItem ag (s1++p++rhs') (item lhs (p++rhs',[]))`
		      by (SRW_TAC [][validItem_def] THEN
			  Q.EXISTS_TAC `h::t` THEN
			  SRW_TAC [][] THEN
			  METIS_TAC [EVERY_DEF,rdres1,rderives_append,APPEND_ASSOC]) THEN
		  Cases_on `p=[]` THEN SRW_TAC [][]
                   THENL[
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      METIS_TAC [transImpValidItem,completeItem_def,itemLhs_def,slrmacCompItemsEq],
			      
			      `?e t.p=e::t` by METIS_TAC [list_nchotomy] THEN
			      SRW_TAC [][] THEN			
			      `(item lhs (e::t' ++ rhs',[])=(item lhs' (rhs',[])))` 
				  by METIS_TAC [transImpValidItem,completeItem_def,itemLhs_def,slrmacCompItemsEq] THEN
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      METIS_TAC [APPEND,APPEND_11,NOT_CONS_NIL]
			      ]		  
			]
		  ],
      
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      METIS_TAC [slrmacConf1,EVERY_APPEND],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      METIS_TAC [slrmacConf1,EVERY_APPEND]
      ])       
		       
		       


val ambThm0 = store_thm
("ambThm0",
 ``(auggr g st eof = SOME ag) ==>
 (!nt.nt ∈ nonTerminals ag ==> gaw ag nt) ==> 
 (slrmac ag = SOME m) ==>
  rtc2list (rderives ag) dl ==>
 rtc2list (rderives ag) dl' ==>
(HD dl = [NTS (startSym ag)]) ==>
 (HD dl = HD dl') ==>
 (LAST dl = LAST dl') ==>
 EVERY isTmnlSym (LAST dl) ==>
 (dl=dl')``,
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
IMP_RES_TAC listDiffSfxSame
THENL[
      SRW_TAC [] [] THEN
      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
      `rsf ag [NTS (startSym ag)]` by METIS_TAC [rsf_def,RTC_RULES] THEN
      `TL ([NTS (startSym ag)]::
                 (t ++ [NTS (startSym ag)]::t')) 
          = (t ++ [NTS (startSym ag)]::t')` by SRW_TAC [][] THEN
      IMP_RES_TAC rtc2listSt THEN
      METIS_TAC [MEM,MEM_APPEND,APPEND,HD],

      SRW_TAC [] [] THEN
      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
      `rsf ag [NTS (startSym ag)]` by METIS_TAC [rsf_def,RTC_RULES] THEN
      `TL ([NTS (startSym ag)]::
                 (t ++ [NTS (startSym ag)]::t')) 
          = (t ++ [NTS (startSym ag)]::t')` by SRW_TAC [][] THEN
      IMP_RES_TAC rtc2listSt THEN
      METIS_TAC [MEM,MEM_APPEND,APPEND,HD],

      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `pfx=[]` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `pfx'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `¬(pfx'++[h']++sfx = [])`by SRW_TAC [][] THEN
      `(pfx'++[h']++sfx = (HD (pfx'++[h']++sfx))::
                           TL (pfx'++[h']++sfx))`
	  by METIS_TAC [listHdTl,APPEND] THEN
      Q.ABBREV_TAC `h = HD (pfx'++[h']++sfx)` THEN
      Q.ABBREV_TAC `tl = TL (pfx'++[h']++sfx)` THEN
      Q.ABBREV_TAC `ls = LAST (pfx'++[h']++sfx)` 
      THENL[
	    `rsf ag h` by METIS_TAC [rsf_def,RTC_RULES] THEN
	    `∀e.MEM e tl ==> rsf ag e` 
		by METIS_TAC [rsfDistribRtc2List] THEN
	    Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] 
           THENL[
		 METIS_TAC [last_append,APPEND,NOT_CONS_NIL,LAST_CONS],
	   
		 `rderives ag h' h'' ` by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
		 FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
		 SRW_TAC [][] THEN
		 FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
		 SRW_TAC [][] THEN
		 FULL_SIMP_TAC (srw_ss()) [] THEN
		 `rhs=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
		 SRW_TAC [][] 
                 THENL[
		       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] 
		       THENL[
		       Cases_on `rhs'` THEN SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `pfx'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] 
               	       THENL[
			     `rderives ag [NTS (startSym g); NTS lhs'; TS eof]
		               [NTS (startSym g); TS eof] ` 
				 by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
			     FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
			     SRW_TAC [][] THEN
			     Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			     Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) []THEN
			     SRW_TAC [][] THEN
			     `RTC (rderives ag) [NTS (startSym ag)] [NTS (startSym g); NTS lhs; TS eof]`
				 by METIS_TAC [rsf_def,MEM,MEM_APPEND,APPEND] THEN
			     `?n.NRC (rderives ag) n [NTS (startSym ag)]
		                 ([NTS (startSym g)]++[NTS lhs]++[TS eof])` 
				 by METIS_TAC [RTC_NRC,APPEND,rdres1,RTC_RULES,APPEND_NIL] THEN
			     `∃s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) 
				  = SOME s) ∧
		                   MEM (item lhs ([],[])) s` by METIS_TAC [lemma] THEN
			     `validItem ag [NTS (startSym g)] 
		                   (item (startSym ag) ([NTS (startSym g)],[TS eof]))` 
				 by (SRW_TAC [] [validItem_def] THEN
				     MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
				     SRW_TAC [] [RTC_RULES]  THEN
				     METIS_TAC [rdres1]) THEN
			     `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof]))
		              s` by METIS_TAC [transImpValidItem] THEN
			     `(TS eof) IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN	   
			     METIS_TAC [slrmacNotValid,isTmnlSym_def,sgoto_exp],
			     
			     METIS_TAC [auggrEofInRhs,APPEND,NOT_CONS_NIL]
			     ],
	   

		       (*cases on t'*)
		       SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       `RTC (rderives ag) [NTS (startSym ag)] [NTS (startSym g);TS eof;NTS lhs']`
			   by METIS_TAC [rsf_def,MEM,MEM_APPEND,APPEND] THEN
		       `[NTS (startSym g); TS eof; NTS lhs'] =
         		 [NTS (startSym g); TS eof] ++[NTS lhs']++[]`
			   by METIS_TAC [APPEND,APPEND_NIL] THEN
		       Cases_on `lhs'=startSym ag` 
			THENL[
			      METIS_TAC [APPEND,auggrRtcRderivesPfxSfxNil,NOT_CONS_NIL],
			      
			      METIS_TAC [MEM,MEM_APPEND,lastEof]
			      ]
		       ],

		       
		       Cases_on `s2'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] 
		       THENL[
                       Cases_on `s1'` THEN
		       Cases_on `rhs'` THEN SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `pfx'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] 
               	       THENL[
			     Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     `rsf ag [NTS lhs'; TS eof]`
				 by METIS_TAC [MEM,MEM_APPEND] THEN
			     FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
			     `?n.NRC (rderives ag) n [NTS (startSym ag)]
		                 ([]++[NTS lhs']++[TS eof])` 
				 by METIS_TAC [RTC_NRC,APPEND,rdres1,RTC_RULES,APPEND_NIL] THEN
			     `∃s.(trans ag (initItems ag (rules ag),[]) 
				  = SOME s) ∧
		                   MEM (item lhs' ([],[NTS (startSym g)])) s` by METIS_TAC [lemma] THEN
			     FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			     SRW_TAC [][] THEN
			     `MEM (rule (startSym ag) [NTS (startSym g); TS eof])
				   (rules ag)` by METIS_TAC [auggrNewRuleMem] THEN
			     `MEM (item (startSym ag) ([],[NTS (startSym g);TS eof]))
				   (initItems ag (rules ag))` by METIS_TAC [memInitProds] THEN
			     `(TS eof) IN (followSet ag (NTS lhs'))`
				 by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN	   
			     `?s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) = SOME s)
                               /\ MEM (item lhs' ([NTS (startSym g)],[])) s 
                               /\ MEM (item (startSym ag) ([NTS (startSym g)],[TS eof])) s`
				 by (SRW_TAC [][] THEN
				     FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
				     `MEM (item lhs' ([NTS (startSym g)],[]))
                                 (moveDot (initItems ag (rules ag)) (NTS (startSym g)))`
					 by METIS_TAC [APPEND,mdMemExists] THEN
				     `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof]))
                                 (moveDot (initItems ag (rules ag)) (NTS (startSym g)))`
					 by METIS_TAC [APPEND,mdMemExists] THEN
				     Cases_on `moveDot (initItems ag (rules ag)) (NTS (startSym g))` THEN
				     FULL_SIMP_TAC (srw_ss()) [] THEN
				     METIS_TAC [iclosure_mem,MEM]) THEN
			     METIS_TAC [slrmacNotValid,isTmnlSym_def,sgoto_exp],

			     Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     `RTC (rderives ag) [NTS (startSym ag)] [NTS (startSym g); NTS lhs'; TS eof]`
				 by METIS_TAC [rsf_def,MEM,MEM_APPEND,APPEND] THEN
			     `?n.NRC (rderives ag) n [NTS (startSym ag)]
		                 ([NTS (startSym g)]++[NTS lhs']++[TS eof])` 
				 by METIS_TAC [RTC_NRC,APPEND,rdres1,RTC_RULES,APPEND_NIL] THEN
			     `∃s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) 
				  = SOME s) ∧
		                   MEM (item lhs' ([],[])) s` by METIS_TAC [lemma] THEN
			     `validItem ag [NTS (startSym g)] 
		                   (item (startSym ag) ([NTS (startSym g)],[TS eof]))` 
				 by (SRW_TAC [] [validItem_def] THEN
				     MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
				     SRW_TAC [] [RTC_RULES]  THEN
				     METIS_TAC [rdres1]) THEN
			     `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof]))
		              s` by METIS_TAC [transImpValidItem] THEN
			     `(TS eof) IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN	   
			     METIS_TAC [slrmacNotValid,isTmnlSym_def,sgoto_exp],
			     
			     Cases_on `t'` THEN SRW_TAC [][] THEN
			     FULL_SIMP_TAC (srw_ss()) []
			     ],
	   
		       
		       (*cases on s2'*)
		       Cases_on `s1'` THEN 
		       Cases_on `rhs'` THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [] [] THEN
		       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
		       Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []
		       ],

		       Cases_on `s1'` THEN
		       Cases_on `rhs'` THEN
		       Cases_on `s2'` THEN
		       SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
                       THENL[
			     METIS_TAC [auggrEofInRhs,APPEND,APPEND_NIL],

			     SRW_TAC [][] THEN
			     Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     Cases_on `pfx'` THEN SRW_TAC [][] THEN
			     FULL_SIMP_TAC (srw_ss()) [] THEN
			     `rderives ag [NTS lhs'; TS eof] [NTS (startSym g); TS eof]`
			     by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
			     `rsf ag [NTS lhs'; TS eof]` by METIS_TAC [MEM,MEM_APPEND] THEN
			     FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
			     `?n.NRC (rderives ag) n [NTS (startSym ag)]
                		       [NTS lhs'; TS eof]` by METIS_TAC [RTC_NRC] THEN
			     `MEM (item lhs' ([],[NTS (startSym g)])) (initItems ag (rules ag))`
			     by METIS_TAC [initItemsHdNt,APPEND] THEN
			     `MEM (item (startSym ag) ([],[NTS (startSym g);TS eof]))
				       (initItems ag (rules ag))` 
				 by METIS_TAC [memInitProds] THEN
			     `?s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) = SOME s)
                               /\ MEM (item (startSym ag)
					     ([NTS (startSym g)], [TS eof])) s
                               /\ MEM (item lhs' ([NTS (startSym g)],[])) s`
			     by (SRW_TAC [] [trans_def] THEN
				 Cases_on `moveDot (initItems ag (rules ag)) (NTS (startSym g))` THEN
				 SRW_TAC [][] THEN
				 METIS_TAC [mdMemExists,APPEND,MEM,iclosure_mem]) THEN
			     `(TS eof) IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN			     
			     METIS_TAC [slrmacNotValid,sgoto_exp,isTmnlSym_def],


			     `rsf ag [NTS (startSym g); TS eof; NTS lhs']`
			     by METIS_TAC [MEM,MEM_APPEND,APPEND] THEN
			     `[NTS (startSym g); TS eof; NTS lhs']=[NTS (startSym g); TS eof] ++[NTS lhs']++[]`
				 by METIS_TAC [APPEND,APPEND_NIL] THEN
			     METIS_TAC [lastEof,MEM,MEM_APPEND,rsf_def],

			     Cases_on `t'` THEN
			     FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     Cases_on `pfx'` THEN SRW_TAC [][] THEN
			     FULL_SIMP_TAC (srw_ss()) [] THEN
			     `rderives ag [NTS (startSym g); NTS lhs'; TS eof] [NTS (startSym g); TS eof]`
			     by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
			     `rsf ag [NTS (startSym g); NTS lhs'; TS eof]` by METIS_TAC [MEM,MEM_APPEND] THEN
			     FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
			     `?n.NRC (rderives ag) n [NTS (startSym ag)]
                		       ([NTS (startSym g)]++[NTS lhs']++[TS eof])` by METIS_TAC [RTC_NRC,APPEND] THEN
			     IMP_RES_TAC lemma THEN
			     `MEM (item (startSym ag) ([],[NTS (startSym g);TS eof]))
				       (initItems ag (rules ag))` 
				 by METIS_TAC [memInitProds] THEN
			     `validItem ag [NTS (startSym g)] (item (startSym ag) ([NTS (startSym g)],[TS eof]))`
				 by (SRW_TAC [] [validItem_def] THEN
				     MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
				     SRW_TAC [][] THEN
				     METIS_TAC [rdres1,rderives_append]) THEN
			     `(TS eof) IN (followSet ag (NTS lhs'))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN			     
			     METIS_TAC [slrmacNotValid,sgoto_exp,isTmnlSym_def,transImpValidItem],


			     Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     SRW_TAC [][] THEN
			     METIS_TAC [auggrEofInRhs,APPEND_NIL],

			     Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []
			     
			     ]]],


		 Cases_on `sfx=[]` THEN
		 SRW_TAC [][] THEN
		 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
		 `∃e t.sfx=e::t` by METIS_TAC [list_nchotomy] THEN
		 SRW_TAC [][] THEN
		 Cases_on `pfx` THEN SRW_TAC [][] THEN
		 FULL_SIMP_TAC (srw_ss()) [] THEN
		 `rsf ag [NTS (startSym ag)]` by METIS_TAC [rsf_def,RTC_RULES] THEN
		 `rderives ag h e`by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
		 FULL_SIMP_TAC (srw_ss()) [rderives_def,lreseq] THEN
		 SRW_TAC [][] THEN
		 `s1++rhs++s2=[NTS (startSym g);TS eof]`
		 by METIS_TAC [auggrStartRule] THEN
		 Cases_on `s1` THEN
		 Cases_on `rhs` THEN
		 Cases_on `s2` THEN
		 FULL_SIMP_TAC (srw_ss()) [] THEN
		 SRW_TAC [][] THEN
		 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
		 THENL[
		       METIS_TAC [auggrEofInRhs,APPEND,APPEND_NIL],

		       Cases_on `t''` THEN SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       IMP_RES_TAC rsfDistribRtc2List THEN
		       `rsf ag [NTS lhs; TS eof]` by METIS_TAC [rsfDistribRtc2List,MEM,MEM_APPEND,APPEND] THEN
		       FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
		       `?n.NRC (rderives ag) n [NTS (startSym ag)]
         		 ([]++[NTS lhs]++[TS eof])` 
			   by METIS_TAC [RTC_NRC,APPEND,rdres1,RTC_RULES,APPEND_NIL] THEN
		       `∃s.(trans ag (initItems ag (rules ag),[]) 
				  = SOME s) ∧
		                   MEM (item lhs ([],[NTS (startSym g)])) s` by METIS_TAC [lemma] THEN
			     FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			     SRW_TAC [][] THEN
			     `MEM (rule (startSym ag) [NTS (startSym g); TS eof])
				   (rules ag)` by METIS_TAC [auggrNewRuleMem] THEN
			     `MEM (item (startSym ag) ([],[NTS (startSym g);TS eof]))
				   (initItems ag (rules ag))` by METIS_TAC [memInitProds] THEN
			     `(TS eof) IN (followSet ag (NTS lhs))`
				 by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN	   
 			     `?s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) = SOME s)
                               /\ MEM (item lhs ([NTS (startSym g)],[])) s 
                               /\ MEM (item (startSym ag) ([NTS (startSym g)],[TS eof])) s`
				 by (SRW_TAC [][] THEN
				     FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
				     `MEM (item lhs ([NTS (startSym g)],[]))
                                 (moveDot (initItems ag (rules ag)) (NTS (startSym g)))`
					 by METIS_TAC [APPEND,mdMemExists] THEN
				     `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof]))
                                 (moveDot (initItems ag (rules ag)) (NTS (startSym g)))`
					 by METIS_TAC [APPEND,mdMemExists] THEN
				     Cases_on `moveDot (initItems ag (rules ag)) (NTS (startSym g))` THEN
				     FULL_SIMP_TAC (srw_ss()) [] THEN
				     METIS_TAC [iclosure_mem,MEM]) THEN
			     METIS_TAC [slrmacNotValid,isTmnlSym_def,sgoto_exp],


		       IMP_RES_TAC rsfDistribRtc2List THEN
		       `rsf ag [NTS (startSym g); TS eof; NTS lhs]`
			   by METIS_TAC [APPEND,MEM,MEM_APPEND] THEN
		       FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
		       Cases_on `lhs=startSym ag`
		       THENL[
			     METIS_TAC [auggrStartRule,APPEND,NOT_CONS_NIL],

			     `[NTS (startSym g); TS eof; NTS lhs]=
                              [NTS (startSym g); TS eof]++[NTS lhs]++[]`
				 by METIS_TAC [APPEND,APPEND_ASSOC,APPEND_NIL] THEN
			     METIS_TAC [MEM,MEM_APPEND,lastEof]
			     ],



		       Cases_on `t''` THEN SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN	
		       SRW_TAC [][] THEN
		       IMP_RES_TAC rsfDistribRtc2List THEN
		       `rsf ag [NTS (startSym g); NTS lhs; TS eof]`
			   by METIS_TAC [APPEND,MEM,MEM_APPEND] THEN
		       FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
		       `?n.NRC (rderives ag) n [NTS (startSym ag)]
		                 ([NTS (startSym g)]++[NTS lhs]++[TS eof])` 
				 by METIS_TAC [RTC_NRC,APPEND,rdres1,RTC_RULES,APPEND_NIL] THEN
			     `∃s.(trans ag (initItems ag (rules ag),[NTS (startSym g)]) 
				  = SOME s) ∧
		                   MEM (item lhs ([],[])) s` by METIS_TAC [lemma] THEN
			     `validItem ag [NTS (startSym g)] 
		                   (item (startSym ag) ([NTS (startSym g)],[TS eof]))` 
				 by (SRW_TAC [] [validItem_def] THEN
				     MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
				     SRW_TAC [] [RTC_RULES]  THEN
				     METIS_TAC [rdres1]) THEN
			     `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof]))
		              s` by METIS_TAC [transImpValidItem] THEN
			     `(TS eof) IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN	   
			     METIS_TAC [slrmacNotValid,isTmnlSym_def,sgoto_exp],

		       Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       METIS_TAC [auggrEofInRhs,APPEND,NOT_CONS_NIL],

		       Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) []
		       ],


		 Cases_on `pfx` THEN 
		 Cases_on `pfx'` THEN
		 Cases_on `sfx` THEN
		 FULL_SIMP_TAC (srw_ss()) [] THEN
		 SRW_TAC [][] THEN
		 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]
		 THENL[
		       `LAST ([NTS (startSym ag)]::(t ++ [h])) = LAST [h]`
		       by METIS_TAC [last_append,APPEND,APPEND_ASSOC,NOT_CONS_NIL] THEN
		       `LAST (h''''::(t' ++ [h'])) = LAST [h']`
			   by METIS_TAC [last_append,APPEND,APPEND_ASSOC,NOT_CONS_NIL] THEN
		       FULL_SIMP_TAC (srw_ss()) [],

		       `rderives ag h h'''''` 
			   by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
		       `rderives ag h' h'''''` 
			   by METIS_TAC [rtc2listRd,APPEND,APPEND_ASSOC] THEN
		       IMP_RES_TAC rsfDistribRtc2List THEN
		       `rsf ag h` by METIS_TAC [APPEND,MEM_APPEND,MEM,rsf_def,RTC_RULES] THEN
		       `rsf ag h'` by METIS_TAC [APPEND,MEM_APPEND,MEM,rsf_def,RTC_RULES] THEN
		       FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
		       SRW_TAC [] [] THEN
		       UNABBREV_ALL_TAC  THEN
		       FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       METIS_TAC [slrmacConf,EVERY_APPEND]
		       ]]])
		       

val ambThm = store_thm ("ambThm",
``(auggr g st eof = SOME ag) ⇒
       (∀nt. nt ∈ nonTerminals ag ⇒ gaw ag nt) ⇒
       (slrmac ag = SOME m) ⇒
       isUnambiguous0 ag``,
SRW_TAC [] [isUnambiguous0,listderiv_def,language_def,
	    EXTENSION] THEN
METIS_TAC [ambThm0])
