open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory


open listLemmasTheory relationLemmasTheory grammarDefTheory
     regexpTheory parseTreeTheory pdaDefTheory

val _ = new_theory "pumpingLemma";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

val isCnf = Define 
`isCnf g = ∀l r.MEM (rule l r) (rules g) ⇒
    ((LENGTH r = 2) ∧ EVERY isNonTmnlSym r) ∨
    ((LENGTH r = 1) ∧ EVERY isTmnlSym r)`;

val lendist = store_thm 
("lendist",
``∀dl.distElemLen ((pfx++rhs++s2)::l) dl ⇒ 
 distElemLen ((pfx++[NTS lhs]++s2)::(pfx++rhs++s2)::l) ((NTS lhs::s2)::dl)``,

Induct_on `dl` THEN SRW_TAC [][] THEN

FULL_SIMP_TAC (srw_ss()) [distElemLen_def, distinctldNts_def, ldNts_def, rmDupes,
			  isNonTmnlSym_def, FILTER_APPEND] THEN
MAGIC);

val lpow = Define `lpow l i = REPLICATE i l`;

val rtc_lderives_same_append_right = store_thm 
("rtc_lderives_same_append_right",
        ``∀u v.RTC (lderives g) u v 
              ⇒
	      RTC (lderives g) (u++x) (v++x)``,
        HO_MATCH_MP_TAC RTC_INDUCT THEN
        METIS_TAC [RTC_RULES,lderives_same_append_right]);

val powGt = store_thm
("powGt",
``1 ≤ k ∧ m ≥ 2 ** k ⇒ m > 2**(k-1)``,
SRW_TAC [][GREATER_EQ, GREATER_DEF] THEN 
MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN 
Q.EXISTS_TAC `2 ** k` THEN SRW_TAC [ARITH_ss][]);

val existsThrice = store_thm
("existsThrice",
``EXISTS ($~ o $~ o $~ o isTmnlSym) p0 = EXISTS ($~ o isTmnlSym) p0``,

Induct_on `p0` THEN SRW_TAC [][]);


val cnfRtcdPfxSfx = store_thm
("cnfRtcdPfxSfx",
``∀dl z z'.
(lderives g) ⊢ dl ◁ z → z' ∧
isCnf g ∧
MEM (NTS B) (ldNts (TL dl)) ∧ MEM  (v++[NTS B]++x) (TL dl)
 ⇒
(v≠[]) ∨ (x≠[])``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [lderives_def, isCnf] THEN
      SRW_TAC [][] THEN
      RES_TAC 
      THENL[      
	    FULL_SIMP_TAC (srw_ss()) [list_lem2]  THEN
	    SRW_TAC [][] THEN
	    Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] 
	    THENL[
		  Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [NOT_CONS_NIL],

		  Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],

	    FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
	    SRW_TAC [][] THEN
	    Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	    Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) []
	    THENL[
		  Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [],

		  Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) []
		  ]],

      FULL_SIMP_TAC (srw_ss()) [memldNts] THEN
      SRW_TAC [][] THEN
      METIS_TAC [MEM,MEM_APPEND,symbol_11]]);

val symProp = Define
`symProp dl = 
    ∃p tsl B sfx v w s.
     (dl = p ++ [tsl ++ [NTS B] ++ sfx] ++ s) ∧
     EVERY isTmnlSym tsl ∧
     ∃s0 s1.(s = s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1) ∧
     EVERY isTmnlSym v ∧
     (∀e.MEM e s0 ⇒ ∃p0 p1 nt.(e = tsl ++ p0 ++ [NTS nt] ++ p1 ++ sfx) ∧ 
      EVERY isTmnlSym p0)`;


val spropApp = store_thm
("spropApp",
``∀dl.(dl≠[]) ∧  ¬symProp dl ⇒
¬symProp (TL dl)``,

Induct_on `dl` THEN SRW_TAC [][symProp] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [symProp] THEN
Cases_on `p` THEN SRW_TAC [][] THEN1
 (FIRST_X_ASSUM (Q.SPECL_THEN [`[h]`,`tsl`,`B`,`sfx`,`v`,`w`, `t`]
		 MP_TAC) THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [MEM,MEM_APPEND]) THEN

 FIRST_X_ASSUM (Q.SPECL_THEN [`h::h''::t'`,`tsl`,`B`,`sfx`,`v`,`w`,`s`]
		MP_TAC) THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [MEM,MEM_APPEND]);

val splitDerivProp =
Define `splitDerivProp (g,dl,v) (dl1,x,x') (dl2,y,y') =
 (v = x' ++ y') ∧
 (lderives g) ⊢ dl1 ◁ x → x' ∧
 (lderives g) ⊢ dl2 ◁ y → y' ∧
 (LENGTH dl1 ≤ LENGTH dl) ∧
 (LENGTH dl2 ≤ LENGTH dl) ∧
 distElemSubset dl dl1 ∧
 distElemSubset dl dl2 ∧
  (dl = MAP ((λe l.addLast l e) y) dl1 ++ 
		     MAP (addFront x') (TL dl2)) ∧
  ¬symProp dl1 ∧ ¬symProp dl2 ∧ distElemLen dl dl1 ∧ distElemLen dl dl2 ∧    
 (LENGTH (distinctldNts dl2) ≤ LENGTH (distinctldNts dl))`;


val l1 = prove 
(``EVERY isTmnlSym x ⇒ [x] ≠ p ++ [tsl ++ [NTS B] ++ sfx'] ++ s``,

SRW_TAC [][lreseq] THEN
Q_TAC SUFF_TAC `tsl ++ [NTS B] ++ sfx' ≠ x` THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);

val leftmostAddFront = store_thm
("leftmostAddFront",
 ``∀l h s2.(∀e.MEM e l ⇒ ∃p0 p1 nt.(e = p0 ++ [NTS nt] ++ p1 ++ s2) ∧
       EVERY isTmnlSym p0) ∧ EVERY isTmnlSym h ⇒
 (∀e.MEM e (MAP (addFront h) l) ⇒
  ∃p0 p1 nt.(e = p0 ++ [NTS nt] ++ p1 ++ s2) ∧
  EVERY isTmnlSym p0)``,
 
 Induct_on `l` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
 `∃p0 p1 nt.
 (h = p0 ++ [NTS nt] ++ p1 ++ s2) ∧ EVERY isTmnlSym p0`
 by METIS_TAC [] THEN
 SRW_TAC [][] THEN1
 METIS_TAC [EVERY_APPEND] THEN
IMP_RES_TAC addFrontMem THEN
SRW_TAC [][] THEN
RES_TAC THEN
SRW_TAC [][]);

val leftmostAddFront' = store_thm
("leftmostAddFront'",
 ``∀l h s2.(∀e.MEM e l ⇒ ∃p0 p1 nt.(e = p0 ++ [NTS nt] ++ p1 ++ s2) ∧
       EVERY isTmnlSym p0) ∧ EVERY isTmnlSym h ⇒
 (∀e.MEM e (MAP (addFront h) l) ⇒
  ∃p0 p1 nt.(e = h ++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧
  EVERY isTmnlSym p0)``,
 
 Induct_on `l` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
 `∃p0 p1 nt.
 (h = p0 ++ [NTS nt] ++ p1 ++ s2) ∧ EVERY isTmnlSym p0`
 by METIS_TAC [] THEN
 SRW_TAC [][] THEN1
 METIS_TAC [EVERY_APPEND] THEN
IMP_RES_TAC addFrontMem THEN
SRW_TAC [][] THEN
RES_TAC THEN
SRW_TAC [][]);

val leftmostAddLast' = store_thm
("leftmostAddLast'",
 ``∀l h s2.(∀e.MEM e l ⇒ ∃p0 p1 nt.(e = p0 ++ [NTS nt] ++ p1 ++ s2) ∧
       EVERY isTmnlSym p0) ⇒
 (∀e.MEM e (MAP (λl'.addLast l' h) l) ⇒
  ∃p0 p1 nt.(e = p0 ++ [NTS nt] ++ p1 ++ s2 ++ h) ∧
  EVERY isTmnlSym p0)``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [addLast_def]);
 

val ldSplitDeriv = store_thm
("ldSplitDeriv",
``∀x y v pfx sfx.
 (lderives g) ⊢ dl ◁ (x ++ y) → v  ∧ isCnf g ∧
 EVERY isTmnlSym v ∧ 
 (pfx++sfx = x++y) ∧ EVERY isTmnlSym pfx ∧ EVERY isNonTmnlSym sfx ∧
 ¬symProp dl
  ⇒
  ∃dl1 dl2 x' y'.
  splitDerivProp (g,dl,v) (dl1,x,x') (dl2,y,y')``,

completeInduct_on `LENGTH dl` THEN 
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def, symProp] THEN
 SRW_TAC [][] THEN
 Q.EXISTS_TAC `[x]` THEN
 Q.EXISTS_TAC `[y]` THEN
 SRW_TAC [][] THEN
SRW_TAC [][distElemSubset_def, distElemLen_def, addLast_def, addFront_def] THEN
METIS_TAC [lendistNtsApp',APPEND_NIL,APPEND_NIL,EVERY_APPEND,
 memdistNtsApp',memdistNtsApp, l1, addLast_def]) THEN

Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`lderives g h h' ∧ lderives g ⊢ h'::t' ◁ h' → v'` 
by METIS_TAC [listDerivHdBrk] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((s1 ++ rhs ++ s2)::t')`] MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`((s1 ++ rhs ++ s2)::t')`] MP_TAC) THEN
SRW_TAC [][] THEN

`¬symProp ((s1++rhs++s2)::t')` by METIS_TAC [spropApp,TL,NOT_CONS_NIL] THEN
`(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
    (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs`
by METIS_TAC [isCnf]
THENL[
      `x++y = (s1 ++ [NTS lhs] ++ s2)` 
      by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `(s1=pfx) ∧(sfx=[NTS lhs]++s2)` by METIS_TAC [symListDiv] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC listCompLens THEN
      SRW_TAC [][] 
      THENL[
	    `y=[NTS lhs]++s2` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`rhs++s2`,`v'`,`pfx`,`rhs++s2`] 
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl1` THEN
	    Q.EXISTS_TAC `(NTS lhs::s2)::dl2` THEN
	    Q.EXISTS_TAC `x''` THEN
	    Q.EXISTS_TAC `y''` THEN
	    SRW_TAC [][]  THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN1
	    (Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [lderives_def,APPEND,APPEND_NIL,EVERY_APPEND]) THEN1      
	    DECIDE_TAC THEN1                  
	    METIS_TAC [desApp, APPEND, APPEND_NIL] THEN1	    
	    METIS_TAC [memdist, APPEND_NIL] THEN1
	    (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
	     SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	     (SRW_TAC [][addLast_def, addFront_def] THEN 
	      METIS_TAC [APPEND, APPEND_ASSOC]) THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [addFront_def, addLast_def]) THEN1

	    (SPOSE_NOT_THEN ASSUME_TAC THEN      
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symProp] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
	     Cases_on `e1` THEN Cases_on `e2` THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN1
	     (* p =[] *)
	     (`tsl = []` by (Cases_on `tsl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			     Cases_on `h` THEN 
			     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
	      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      Cases_on `dl1` THEN 
	      FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	      SRW_TAC [][] THEN
	      Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][]
	      THENL[
		    `v=[]` by (Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			       Cases_on `h'` THEN 
			       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
		    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN
		    `[NTS n'] = w` by METIS_TAC [APPEND_11, APPEND] THEN
		    SRW_TAC [][] THEN
		    `(h ++ [NTS B] ++ s2)::(h ++ [NTS B] ++ [NTS n'] ++ s2)::
		    (MAP (λl. l ++ [NTS B] ++ [NTS n'] ++ s2) t'' ++
		     MAP (addFront (LAST (h::t''))) s1) =
		    [] ++ [h ++ [NTS B] ++ s2] ++ 
		    ((h ++ [NTS B] ++ [NTS n'] ++ s2)::
		    (MAP (λl. l ++ [NTS B] ++ [NTS n'] ++ s2) t'' ++
		     MAP (addFront (LAST (h::t''))) s1))` 
		    by METIS_TAC [APPEND, APPEND_NIL]  THEN
		    `(h ++ [NTS B] ++ [NTS n'] ++ s2)::
		    (MAP (λl. l ++ [NTS B] ++ [NTS n'] ++ s2) t'' ++
		     MAP (addFront (LAST (h::t''))) s1) = 
		    [] ++ [h ++ [] ++ [NTS B] ++ [NTS n'] ++ s2] ++ 
		    (MAP (λl. l ++ [NTS B] ++ [NTS n'] ++ s2) t'' ++
		     MAP (addFront (LAST (h::t''))) s1)`
		    by METIS_TAC [APPEND, APPEND_NIL] THEN
		    `¬EXISTS ($~ o isTmnlSym) []` by METIS_TAC [NOT_EVERY,
								EVERY_DEF] THEN
		    `¬EXISTS ($~ o isTmnlSym) h` by METIS_TAC [NOT_EVERY] THEN
		    METIS_TAC [MEM],
		    
		    FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		    `t'' = []` by METIS_TAC [rtc2listRtcldTmnls] THEN
		    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    `(h ++ [NTS B] ++ s2)::(h ++ NTS n::NTS n'::s2)::
		    (MAP (addFront h) t' ++ [h ++ v ++ [NTS B] ++ w ++ s2] ++
		     MAP (addFront h) s1) =
		    [] ++ [h ++ [NTS B] ++ s2] ++ 
		    (h ++ NTS n::NTS n'::s2)::
		    (MAP (addFront h) t' ++ [h ++ v ++ [NTS B] ++ w ++ s2] ++
		     MAP (addFront h) s1)` by METIS_TAC [APPEND, APPEND_NIL] THEN
		    `¬EXISTS ($~ o isTmnlSym) h` by METIS_TAC [NOT_EVERY] THEN
		    `¬EXISTS ($~ o isTmnlSym) v` by METIS_TAC [NOT_EVERY] THEN
		    `(h ++ NTS n::NTS n'::s2)::
		    (MAP (addFront h) t' ++ [h ++ v ++ [NTS B] ++ w ++ s2] ++
		     MAP (addFront h) s1) = ((h ++ NTS n::NTS n'::s2)::
		    (MAP (addFront h) t')) ++ [h ++ v ++ [NTS B] ++ w ++ s2] ++
		     MAP (addFront h) s1` by METIS_TAC [APPEND_ASSOC, APPEND] THEN
		    `(h ++ NTS n::NTS n'::s2)::(MAP (addFront h) t')
		     = MAP (addFront h) ((NTS n::NTS n'::s2)::t')`
		    by SRW_TAC [][addFront_def] THEN
		    `∀e.MEM e ((NTS n::NTS n'::s2)::t') ⇒
		     ∃p0 p1 nt.
		     (e = p0 ++ [NTS nt] ++ p1 ++ s2) ∧
		     EVERY isTmnlSym p0` by METIS_TAC [MEM] THEN
		    `∀e. MEM e (MAP (addFront h) ((NTS n::NTS n'::s2)::t'))
		     ⇒ ∃p0 p1 nt.(e = h ++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧
		     EVERY isTmnlSym p0` by MAGIC (* METIS_TAC [leftmostAddFront'] *)THEN
		    MAGIC(* METIS_TAC [NOT_EVERY, addFront_def] *)
		    ]) THEN

	     Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     Cases_on `t'''` THEN FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   `MAP (addFront h) ((NTS n::NTS n'::s2)::t) =
		   MAP (addFront h) (t'' ++ [tsl ++ [NTS B] ++ sfx] ++ s0 ++
		   [tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1)`
		   by METIS_TAC [] THEN
		   FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		   SRW_TAC [][] THEN
		   `(h ++ [NTS lhs] ++ s2)::(MAP (addFront h) t'') ++
		   [h ++ tsl ++ [NTS B] ++ sfx] ++ MAP (addFront h) s0 ++
		   [h ++ tsl ++ v ++ [NTS B] ++ w ++ sfx] ++
		   MAP (addFront h) s1 =
		   (h ++ [NTS lhs] ++ s2)::(MAP (addFront h) t'') ++ 
		   [(h++tsl) ++ [NTS B] ++ sfx] ++ 
		   (MAP (addFront h) s0 ++
		    [h ++ tsl ++ v ++ [NTS B] ++ w ++ sfx] ++
		    MAP (addFront h) s1)` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
		   `¬ EXISTS ($~ o isTmnlSym) (h++tsl)`
		   by METIS_TAC [NOT_EVERY, EVERY_APPEND] THEN
		   `¬ EXISTS ($~ o isTmnlSym) v`
		   by METIS_TAC [NOT_EVERY] THEN
		   `∀e.
		   MEM e (MAP (addFront h) s0) ⇒
		   ∃p0 p1 nt.
		   (e = h ++ tsl ++ p0 ++ [NTS nt] ++ p1 ++ sfx) ∧
		   EVERY isTmnlSym p0` by MAGIC (* METIS_TAC [leftmostAddFront',
						     APPEND_ASSOC] *) THEN
		   MAGIC (* METIS_TAC [NOT_EVERY] *),

		   FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
		   SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
		   ]) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN1
	    METIS_TAC [lendist', APPEND_NIL, APPEND, APPEND_ASSOC] THEN
	    METIS_TAC [distLenAddElem2,APPEND_NIL,APPEND,APPEND_ASSOC],

	    `y=sfx`by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`pfx++rhs++pfx'`,`sfx`,`v'`,
					 `pfx`,`rhs++pfx'++sfx`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `(pfx++[NTS lhs]++pfx')::dl1` THEN
	    Q.EXISTS_TAC `dl2` THEN
	    Q.EXISTS_TAC `x''` THEN
	    Q.EXISTS_TAC `y''` THEN
	    SRW_TAC [][] THEN1
	    (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [lderives_def,APPEND,APPEND_NIL,APPEND_ASSOC,
			EVERY_APPEND]) THEN1      
	    DECIDE_TAC THEN1            
	     METIS_TAC [memdist', APPEND_NIL] THEN1
	    METIS_TAC [desApp, APPEND, APPEND_NIL] THEN1
	    SRW_TAC [][addLast_def] THEN1

	    (SPOSE_NOT_THEN ASSUME_TAC THEN      
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symProp] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
	     Cases_on `e1` THEN Cases_on `e2` THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN1
	     (* p =[] *)
	     (`EVERY isNonTmnlSym [NTS lhs]` by SRW_TAC [][isNonTmnlSym_def] THEN
	      `(pfx=tsl) ∧ ([NTS lhs]++pfx' = [NTS B]++sfx')` 
	      by METIS_TAC [symlistdiv3, NOT_CONS_NIL] THEN
	      FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN SRW_TAC [][] THEN
	      Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][]
	      THENL[
		    `[NTS n; NTS n'] = v ++ [NTS B] ++ w`
		    by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
		    Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN1
		    (`(pfx ++ [NTS B] ++ pfx' ++ h)::
		    (pfx ++ [NTS B] ++ [NTS n'] ++ pfx' ++ h)::
		    (MAP (λl. l ++ h) s1 ++ 
		     MAP (addFront 
			  (LAST ((pfx ++ [NTS B] ++ [NTS n'] ++ pfx'):: s1))) t) =
		    [] ++ [pfx ++ [NTS B] ++ (pfx'++h)] ++
		    (pfx ++ [NTS B] ++ [NTS n'] ++ pfx' ++ h)::
		    (MAP (λl. l ++ h) s1 ++ 
		     MAP (addFront 
			  (LAST ((pfx ++ [NTS B] ++ [NTS n'] ++ pfx'):: s1))) t)`
		    by METIS_TAC [APPEND_NIL, APPEND_ASSOC, APPEND] THEN
		    `¬EXISTS ($~ o isTmnlSym) pfx` by METIS_TAC [NOT_EVERY] THEN
		    `(pfx ++ [NTS B] ++ [NTS n'] ++ pfx' ++ h)::
		    (MAP (λl. l ++ h) s1 ++ 
		     MAP (addFront 
			  (LAST ((pfx ++ [NTS B] ++ [NTS n'] ++ pfx'):: s1))) t) =
		    [] ++ [pfx ++ [] ++ [NTS B] ++ [NTS n'] ++ (pfx' ++ h)] ++
		    (MAP (λl. l ++ h) s1 ++ 
		     MAP (addFront 
			  (LAST ((pfx ++ [NTS B] ++ [NTS n'] ++ pfx'):: s1))) t)`
		    by METIS_TAC [APPEND_NIL, APPEND, APPEND_ASSOC] THEN
		    `¬EXISTS ($~ o isTmnlSym) []` by METIS_TAC [NOT_EVERY,
								EVERY_DEF] THEN
		    METIS_TAC [MEM]) THEN
		    FULL_SIMP_TAC (srw_ss()) [lreseq, isTmnlSym_def],


		    FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		    Q.ABBREV_TAC `z=(LAST ((pfx ++ [NTS n; NTS n'] ++ pfx')::
					   (t'' ++ [pfx ++ v ++ [NTS B] ++ w ++ pfx']
					    ++ s1)))` THEN
		    `(pfx ++ [NTS B] ++ pfx' ++ h)::
	      (pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
	      (MAP (λl. l ++ h) t'' ++
	       [pfx ++ v ++ [NTS B] ++ w ++ pfx' ++ h] ++
	       MAP (λl. l ++ h) s1 ++ MAP (addFront z) t) =
	      [] ++ [pfx ++ [NTS B] ++ (pfx'++h)] ++ 
	      (pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
	      (MAP (λl. l ++ h) t'' ++
	       [pfx ++ v ++ [NTS B] ++ w ++ pfx' ++ h] ++
	       MAP (λl. l ++ h) s1 ++ MAP (addFront z) t)`
		    by METIS_TAC [APPEND_ASSOC, APPEND] THEN
		    `¬EXISTS ($~ o isTmnlSym) pfx` by METIS_TAC [NOT_EVERY] THEN
		    `¬EXISTS ($~ o isTmnlSym) v` by METIS_TAC [NOT_EVERY] THEN
		    `(pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
	      (MAP (λl. l ++ h) t'' ++
	       [pfx ++ v ++ [NTS B] ++ w ++ pfx' ++ h] ++
	       MAP (λl. l ++ h) s1 ++ MAP (addFront z) t) = 
	      ((pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
	       (MAP (λl. l ++ h) t'')) ++
	      [pfx ++ v ++ [NTS B] ++ w ++ (pfx' ++ h)] ++
	      (MAP (λl. l ++ h) s1 ++ MAP (addFront z) t)`
		    by METIS_TAC [APPEND_ASSOC, APPEND] THEN
		    `∀e. MEM e ((pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
				(MAP (λl. l ++ h) t''))
	      ⇒ ∃p0 p1 nt.
	      (e = pfx ++ p0 ++ [NTS nt] ++ p1 ++ pfx' ++ h) ∧
	      EVERY isTmnlSym p0` by MAGIC (* METIS_TAC [leftmostAddLast']*) THEN
		    MAGIC (* METIS_TAC [NOT_EVERY, APPEND_ASSOC] *)
		    ]) THEN
	     
	     FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     Q.ABBREV_TAC `s1' =  
	    MAP (addFront (LAST (t'' ++ [tsl ++ [NTS B] ++ sfx'] ++ s0 ++
				 [tsl ++ v ++ [NTS B] ++ w ++ sfx'] ++s1))) t` THEN
	     `(pfx ++ [NTS lhs] ++ pfx' ++ h)::
                (MAP (λl. l ++ h) t'' ++
                 [tsl ++ [NTS B] ++ sfx' ++ h] ++
                 MAP (λl. l ++ h) s0 ++
                 [tsl ++ v ++ [NTS B] ++ w ++ sfx' ++ h] ++
                 MAP (λl. l ++ h) s1 ++ s1') =
		((pfx ++ [NTS lhs] ++ pfx' ++ h)::(MAP (λl. l ++ h) t'')) ++ 
		[tsl ++ [NTS B] ++ (sfx'++h)] ++ 
		MAP (λl. l ++ h) s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx' ++ h] ++
                 MAP (λl. l ++ h) s1 ++ s1'`
	    by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	    `¬EXISTS ($~ o isTmnlSym) tsl` by METIS_TAC [NOT_EVERY] THEN
	    `¬EXISTS ($~ o isTmnlSym) v` by METIS_TAC [NOT_EVERY] THEN
	    `∀e.MEM e (MAP (λl. l ++ h) s0) ⇒
		 ∃p0 p1 nt.(e = tsl ++ p0 ++ [NTS nt] ++ p1 ++ sfx' ++h) ∧
		 EVERY isTmnlSym p0` by MAGIC THEN
	    MAGIC (* METIS_TAC [NOT_EVERY, APPEND_ASSOC, APPEND] *)) THEN1
	    METIS_TAC [lendist', APPEND_NIL] THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN
	    METIS_TAC [distLenAddElem],

	    `y=sfx++[NTS lhs]++s2`by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`pfx'`,`sfx++rhs++s2`,`v'`,
					 `pfx'++sfx`,`rhs++s2`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl1` THEN
	    Q.EXISTS_TAC `(sfx++[NTS lhs]++s2)::dl2` THEN
	    Q.EXISTS_TAC `x''` THEN
	    Q.EXISTS_TAC `y''` THEN
	    SRW_TAC [][] THEN1
	    (Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [lderives_def,APPEND,APPEND_NIL,APPEND_ASSOC,
			EVERY_APPEND]) THEN1      
	    DECIDE_TAC THEN1            
	    METIS_TAC [desApp, APPEND, APPEND_NIL] THEN1
	    METIS_TAC [memdist', APPEND_ASSOC, APPEND_NIL, APPEND] THEN1
	    (Cases_on `dl1` THEN Cases_on `dl2` THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
	     SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [addLast_def, addFront_def]) THEN1

	    (SPOSE_NOT_THEN ASSUME_TAC THEN      
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symProp] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
	     Cases_on `e1` THEN Cases_on `e2` THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN1
	     (* p =[] *)
	     (`EVERY isNonTmnlSym [NTS lhs]` by SRW_TAC [][isNonTmnlSym_def] THEN
	      `(sfx=tsl) ∧ ([NTS lhs]++s2 = [NTS B]++sfx')`
	      by METIS_TAC [symlistdiv3, NOT_CONS_NIL] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	      Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][]
	      THENL[
		    `[NTS n; NTS n'] = v ++ [NTS B] ++ w`
		    by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
		    Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN1
		    (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
		     `¬EXISTS ($~ o isTmnlSym) (h++sfx)`
		     by METIS_TAC [EVERY_APPEND, NOT_EVERY] THEN
		     `(h ++ sfx ++ [NTS B] ++ s2)::
		     (h ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)::
		     (MAP (λl. l ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)
		      t ++ MAP (addFront (LAST (h::t))) s1) =
		     [] ++ [(h++sfx) ++ [NTS B] ++ s2] ++
		     (h ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)::
		     (MAP (λl. l ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)
		      t ++ MAP (addFront (LAST (h::t))) s1)`
		     by METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL] THEN
		     `(h ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)::
		     (MAP (λl. l ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)
		      t ++ MAP (addFront (LAST (h::t))) s1) =
		     [] ++ [(h ++ sfx) ++ [] ++ [NTS B] ++ [NTS n'] ++ s2] ++ 
		     (MAP (λl. l ++ sfx ++ [NTS B] ++ [NTS n'] ++ s2)
		      t ++ MAP (addFront (LAST (h::t))) s1)`
		     by METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL] THEN
		     `¬EXISTS ($~ o isTmnlSym) []`
		     by METIS_TAC [EVERY_DEF, NOT_EVERY] THEN
		     METIS_TAC [MEM]) THEN
		    FULL_SIMP_TAC (srw_ss()) [lreseq, isTmnlSym_def],

		    Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
		    FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		    SRW_TAC [][] THEN
		    `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
		    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    `(h ++ sfx ++ [NTS B] ++ s2)::
	      (h ++ sfx ++ [NTS n; NTS n'] ++ s2)::
	      (MAP (addFront h) t'' ++
	       [h ++ sfx ++ v ++ [NTS B] ++ w ++ s2] ++
	       MAP (addFront h) s1) =
	      [] ++ [(h++sfx) ++ [NTS B] ++ s2] ++ 
	      ((h ++ sfx ++ [NTS n; NTS n'] ++ s2)::
	      (MAP (addFront h) t'' ++
	       [h ++ sfx ++ v ++ [NTS B] ++ w ++ s2] ++
	       MAP (addFront h) s1))` by METIS_TAC [APPEND, APPEND_NIL, 
						    APPEND_ASSOC] THEN
		    `¬EXISTS ($~ o isTmnlSym) (h++sfx)`
		    by METIS_TAC [EVERY_APPEND, NOT_EVERY] THEN
		    `¬EXISTS ($~ o isTmnlSym) v`
		    by METIS_TAC [NOT_EVERY] THEN
 		    `∀e.MEM e ((h ++ sfx ++ [NTS n; NTS n'] ++ s2)::
			       (MAP (addFront h) t'')) ⇒
			       ∃p0 p1 nt.
			       (e = (h++sfx )++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧
			       EVERY isTmnlSym p0` by MAGIC THEN
		    MAGIC(* METIS_TAC [NOT_EVERY, APPEND, APPEND_ASSOC]*)
		    ]) THEN

	     Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     `¬EXISTS ($~ o isTmnlSym) tsl` by METIS_TAC [NOT_EVERY] THEN
	     `¬EXISTS ($~ o isTmnlSym) v` by METIS_TAC [NOT_EVERY] THEN
	     `t'' ++ [tsl ++ [NTS B] ++ sfx'] ++ s0 ++
	    [tsl ++ v ++ [NTS B] ++ w ++ sfx'] ++ s1 =
	    t'' ++ [tsl ++ [NTS B] ++ sfx'] ++ 
	    (s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx'] ++ s1)` 
	     by METIS_TAC [APPEND_ASSOC] THEN
	     MAGIC
	     (* METIS_TAC [NOT_EVERY] *)
	     ) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN1
	    METIS_TAC [lendist', APPEND_ASSOC, APPEND_NIL] THEN
	    METIS_TAC [distLenAddElem2,APPEND_NIL,APPEND,APPEND_ASSOC]
	    ],

      (*tmnl rule*)
      `x++y=(s1 ++ [NTS lhs] ++ s2)` 
      by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      IMP_RES_TAC listCompLens THEN
      SRW_TAC [][]
      THENL[
	    `y=[NTS lhs]++s2` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
	    SRW_TAC [][] THEN
	    `s1=pfx` by METIS_TAC [symListDiv,EVERY_APPEND,APPEND_ASSOC] THEN
	    SRW_TAC [][] THEN
	    `sfx=[NTS lhs]++s2` by METIS_TAC [APPEND_11] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`rhs++s2`,`v'`,
					 `pfx++rhs`,`s2`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl1` THEN
	    Q.EXISTS_TAC `(NTS lhs::s2)::dl2` THEN
	    Q.EXISTS_TAC `x''` THEN
	    Q.EXISTS_TAC `y''` THEN
	    SRW_TAC [][] THEN1
	    
	    (Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [lderives_def,APPEND,APPEND_NIL,EVERY_APPEND]) THEN1      
	    DECIDE_TAC THEN1                  	    
	    METIS_TAC [memdistNtsApp, distElemSubset_def, APPEND] THEN1
	    METIS_TAC [memdist, APPEND_NIL] THEN1
	    (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN1
	     (SRW_TAC [][addLast_def] THEN METIS_TAC [APPEND, APPEND_ASSOC]) THEN
	     `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
	     SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [APPEND,APPEND_ASSOC, addLast_def, addFront_def]) THEN1
	    
	    (FULL_SIMP_TAC (srw_ss()) [symProp] THEN
	     SPOSE_NOT_THEN ASSUME_TAC THEN      
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
	     Cases_on `e` THEN 
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN1
	     (* p=[]  2 subgoals *)
	     (`tsl=[]` by
	      (Cases_on `tsl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	       SRW_TAC [][] THEN
	       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
	      SRW_TAC [][] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]
	      THENL[
		    Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		    SRW_TAC [][] THEN
		    FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
		    Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    `LENGTH (t' ++ [NTS B] ++ w ++ s2) = LENGTH s2`
		    by METIS_TAC [] THEN
		    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],

		    SRW_TAC [][] THEN
		    `∃p0 p1 nt.(TS t::s2= p0 ++ [NTS nt] ++ p1 ++ s2) ∧
		    EVERY ($~ o $~ o isTmnlSym) p0` by METIS_TAC [] THEN
		    `[TS t] = p0++[NTS nt]++p1` by METIS_TAC [APPEND_ASSOC,
							      APPEND_11, APPEND] THEN
		    FULL_SIMP_TAC (srw_ss()) [lreseq]
		    ]) THEN

	     FIRST_X_ASSUM (Q.SPECL_THEN 
			    [`t''`,`tsl`,`B`,`sfx`,`v`,`w`,
			     `s0 ++[tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`] 
			    MP_TAC) THEN
	     SRW_TAC [][] THEN
	     Q.EXISTS_TAC `s0` THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [NOT_EVERY, everyNotTwice]) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN1
	    METIS_TAC [lendist, APPEND_NIL] THEN
	    METIS_TAC [distLenAddElem2,APPEND_NIL,APPEND,APPEND_ASSOC],

	    
	    `y=sfx'`by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `pfx=s1`by METIS_TAC [APPEND_ASSOC,symListDiv] THEN
	    `sfx = [NTS lhs] ++ pfx' ++ sfx'` by METIS_TAC [APPEND_11,
							    APPEND_ASSOC] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`pfx++rhs++pfx'`,`sfx'`,`v'`,
					 `pfx++rhs`,`pfx'++sfx'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `(pfx++[NTS lhs]++pfx')::dl1` THEN
	    Q.EXISTS_TAC `dl2` THEN
	    Q.EXISTS_TAC `x''` THEN
	    Q.EXISTS_TAC `y''` THEN
	    SRW_TAC [][] THEN1
	    (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [lderives_def,APPEND,APPEND_NIL,APPEND_ASSOC,
			EVERY_APPEND]) THEN1      
	    DECIDE_TAC THEN1            	    
	    METIS_TAC [memdist', APPEND_NIL] THEN1
	    METIS_TAC [memdistNtsApp, distElemSubset_def, APPEND] THEN1
	    METIS_TAC [addLast_def, APPEND_ASSOC] THEN1
	    

	    (FULL_SIMP_TAC (srw_ss()) [symProp] THEN
	     SPOSE_NOT_THEN ASSUME_TAC THEN      
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
	     Cases_on `e` THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN1
	     (* p =[] *)
	     (
	      Cases_on `s0` THEN
	      FULL_SIMP_TAC (srw_ss()) [addLast_def] 
	      THENL[
		    `EVERY isNonTmnlSym [NTS lhs]` by 
		    SRW_TAC [] [isNonTmnlSym_def] THEN
		    `(pfx=tsl)` by METIS_TAC [symlistdiv3, NOT_CONS_NIL,
					      everyNotTwice] THEN
		    SRW_TAC [][] THEN
		    `[NTS lhs]++pfx' = [NTS B]++sfx` by METIS_TAC [APPEND_11,
								   APPEND_ASSOC] THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN
		    `EVERY isTmnlSym [TS t'']` by SRW_TAC [][isTmnlSym_def] THEN
		    `EVERY isTmnlSym (pfx ++ v ++ [NTS B] ++ w)`
		    by METIS_TAC [everyNotTwice, EVERY_APPEND] THEN
		    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
		    
		    `EVERY isNonTmnlSym [NTS lhs]` by 
		    SRW_TAC [] [isNonTmnlSym_def] THEN
		    `(pfx=tsl)` by METIS_TAC [symlistdiv3, NOT_CONS_NIL,
					      everyNotTwice] THEN
		    SRW_TAC [][] THEN
		    `[NTS lhs]++pfx' = [NTS B]++sfx` by METIS_TAC [APPEND_11,
								   APPEND_ASSOC] THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN
		    `∃p0 p1 nt.
		    (pfx ++ [TS t''] ++ pfx' = pfx ++ p0 ++ [NTS nt] ++ p1 ++ pfx') ∧
		    EVERY ($~ o $~ o isTmnlSym) p0` by METIS_TAC [] THEN
		    `[TS t''] ++ pfx' = p0 ++ [NTS nt] ++ p1 ++ pfx'`
		    by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
		    `[TS t''] = p0 ++ [NTS nt] ++ p1` by METIS_TAC [APPEND_11,
								    APPEND_ASSOC] THEN
		    FULL_SIMP_TAC (srw_ss()) [lreseq]
		    ]) THEN
	      
	     FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     Q.PAT_ASSUM `∀e.P` MP_TAC THEN
	     Q.PAT_ASSUM `∀e.P` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN 
			    [`t'''`,`tsl`,`B`,`sfx`,`v`,`w`,
			     `s0 ++[tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`] 
			    MP_TAC) THEN
	     SRW_TAC [][] THEN
	     `EXISTS ($~ o $~ o $~ o isTmnlSym) p0 = 
	    EXISTS ($~ o isTmnlSym) p0` by METIS_TAC [existsThrice] THEN
	     METIS_TAC [everyNotTwice, NOT_EVERY]
	     ) THEN1
	    METIS_TAC [lendist', APPEND_NIL] THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN
	    METIS_TAC [distLenAddElem],

	    
	    `y=sfx'++[NTS lhs]++s2`by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `EVERY isTmnlSym (pfx'++sfx')` by METIS_TAC [EVERY_APPEND] THEN
	    `(pfx=pfx'++sfx') ∧ (sfx = [NTS lhs]++s2)` 
	    by METIS_TAC [symListDiv] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`pfx'`,`sfx'++rhs++s2`,`v'`,
					 `pfx'++sfx'++rhs`,`s2`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl1` THEN
	    Q.EXISTS_TAC `(sfx'++[NTS lhs]++s2)::dl2` THEN
	    Q.EXISTS_TAC `x''` THEN
	    Q.EXISTS_TAC `y''` THEN
	    SRW_TAC [][] THEN1
	    (Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [lderives_def,APPEND,APPEND_NIL,APPEND_ASSOC,
			EVERY_APPEND]) THEN1      
	    DECIDE_TAC THEN1            
	    METIS_TAC [memdistNtsApp, distElemSubset_def, APPEND] THEN1
	    METIS_TAC [memdist', APPEND_NIL] THEN1
	    (Cases_on `dl1` THEN Cases_on `dl2` THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
	     SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [addLast_def, addFront_def]) THEN1

	    (SPOSE_NOT_THEN ASSUME_TAC THEN      
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symProp] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
	     Cases_on `e` THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN1
	     (* p =[] *)
	     (	      
	      Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][]
	      THENL[
		    FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
		    SRW_TAC [][] THEN
		    `EVERY isNonTmnlSym [NTS lhs]`
		    by SRW_TAC [][isNonTmnlSym_def] THEN
		    `(sfx'=tsl) ∧ ([NTS lhs]++s2 = [NTS B]++sfx)`
		    by METIS_TAC [symlistdiv3, NOT_CONS_NIL] THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
		    `[TS t''] = v ++ [NTS B] ++ w` 
		    by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
		    FULL_SIMP_TAC (srw_ss()) [lreseq],

		    `EVERY isNonTmnlSym [NTS lhs]`
		    by SRW_TAC [][isNonTmnlSym_def] THEN
		    `(sfx'=tsl) ∧ ([NTS lhs]++s2 = [NTS B]++sfx)`
		    by METIS_TAC [symlistdiv3, NOT_CONS_NIL] THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
		    `∃p0 p1 nt.
		    (sfx' ++ [TS t''] ++ s2 = sfx' ++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧
		    EVERY isTmnlSym p0` by METIS_TAC [] THEN
		    `[TS t''] = p0 ++ [NTS nt] ++ p1` by METIS_TAC [APPEND_ASSOC,
								    APPEND_11] THEN
		    FULL_SIMP_TAC (srw_ss()) [lreseq]
		    ]) THEN

	     FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     Q.PAT_ASSUM `∀e.P` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN 
			    [`t'''`,`tsl`,`B`,`sfx`,`v`,`w`,
			     `s0 ++[tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`] 
			    MP_TAC) THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [everyNotTwice, NOT_EVERY]) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN1
	    METIS_TAC [lendist', APPEND_NIL] THEN
	    METIS_TAC [distLenAddElem2,APPEND_NIL,APPEND,APPEND_ASSOC]
	    ]]);



val powLe  = store_thm
("powLe",
``∀n p p'.n ≤ 2**(p-1) ∧ (p ≤ p') ⇒ n ≤ 2**(p'-1)``,
SRW_TAC [][] THEN MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS THEN 
Q.EXISTS_TAC `2 ** (p - 1)` THEN SRW_TAC [][] THEN DECIDE_TAC);


val powMult = store_thm
("powMult",
``∀n.2*2**n = 2**(n+1)``,

Induct_on `n` THEN SRW_TAC [][] THEN
`SUC n + 1 = SUC (SUC n)` by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][Once EXP] THEN
METIS_TAC [EXP]);

val inpLen = store_thm
("inpLen",
``∀k A z.
    (lderives g) ⊢ (dl:(α,β) symbol list list) ◁ [NTS A] → z ∧ 
    (k = LENGTH (distinctldNts dl)) ∧
    EVERY isTmnlSym z ∧
    isCnf g ∧
    ¬symProp dl
    ⇒
    (LENGTH z ≤ 2**(k - 1))``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ldNts_def,distinctldNts_def, isNonTmnlSym_def,
 rmDupes,delete_def]) THEN
SRW_TAC [][] THEN

`lderives g [NTS A] h' ∧ lderives g ⊢ h'::t' ◁ h' → z` 
 by METIS_TAC [listDerivHdBrk,listderiv_def,HD] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def,lreseq] THEN
 `(LENGTH h' = 2) ∧ EVERY isNonTmnlSym h' ∨
    (LENGTH h' = 1) ∧ EVERY isTmnlSym h'` by METIS_TAC [isCnf,lderives_def,
							APPEND_NIL,lreseq]
THENL[

FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
SRW_TAC [][] THEN
`lderives g ⊢ [e1; e2]::t' ◁ [e1]++ [e2] → z` by METIS_TAC [APPEND] THEN
`∃pfx sfx.
      (pfx++sfx = [e1]++[e2]) ∧
      EVERY isTmnlSym pfx ∧ EVERY isNonTmnlSym sfx` 
      by METIS_TAC [APPEND_NIL,EVERY_DEF,APPEND] THEN
Q.ABBREV_TAC `dl=[e1; e2]::t'` THEN
Q.ABBREV_TAC `el1 = [e1]` THEN
Q.ABBREV_TAC `el2 = [e2]` THEN
`EVERY isNonTmnlSym (el1++el2)` by METIS_TAC [APPEND,EVERY_DEF] THEN
`¬symProp dl` by METIS_TAC [NOT_EVERY,spropApp,TL,NOT_CONS_NIL] THEN
`∀tsl e sfx.LENGTH (tsl ++ [e] ++ sfx) + 1 = LENGTH tsl + 1 + LENGTH sfx + 1`
      by SRW_TAC [][] THEN
`∃dl1 dl2 x' y'.
splitDerivProp (g,dl,z) (dl1,el1,x') (dl2,el2,y')`
      by METIS_TAC [ldSplitDeriv] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e1` THEN Cases_on `e2` THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`LENGTH dl1 < (SUC (SUC (LENGTH t')))` by DECIDE_TAC THEN
`LENGTH dl2 < (SUC (SUC (LENGTH t')))` by DECIDE_TAC THEN
`lderives g ⊢ dl1 ◁ [NTS n] → x' ∧ ¬symProp dl1
⇒
LENGTH x' ≤
2 ** (LENGTH (distinctldNts dl1) − 1)` by METIS_TAC [] THEN
`lderives g ⊢ dl2 ◁ [NTS n'] → y' ∧ ¬symProp dl2  ⇒
	   LENGTH y' ≤
	   2 ** (LENGTH (distinctldNts dl2) − 1)` by METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH x' ≤ 2 ** (LENGTH (distinctldNts dl1) − 1)` by METIS_TAC [symProp,
								  NOT_EVERY] THEN
`LENGTH y' ≤ 2 ** (LENGTH (distinctldNts dl2) − 1)` by METIS_TAC [symProp,
								  NOT_EVERY] THEN
`h=[NTS A]` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [distElemLen_def] THEN
`LENGTH (distinctldNts dl1) ≤
           LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) - 1`
by METIS_TAC [distLenAddElemNew,MEM,APPEND_NIL,distesubaddlist,distElemLen_def,
	    distesub1] THEN
`LENGTH (distinctldNts dl2) ≤
           LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) -1`
by METIS_TAC [distLenAddElemNew,MEM,APPEND_NIL,distesubaddlist,distElemLen_def,
	      distesub2] THEN
`LENGTH x' ≤ 2 ** ((LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) −
           1) − 1)` by METIS_TAC [powLe] THEN
`LENGTH y' ≤ 2 ** ((LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) −
           1) − 1)` by METIS_TAC [powLe] THEN
`LENGTH x' + LENGTH y' ≤ 
	   2*2 ** ((LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) −1) − 1)` 
by DECIDE_TAC THEN
`LENGTH x' + LENGTH y' ≤ 
	   2 ** (((LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) − 1) − 1) 
		 + 1)` by METIS_TAC [powMult] THEN
`(NTS n ≠ NTS A)` by 

(SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [symProp] THEN
 
`[NTS A]::[NTS A; NTS n']::t' =
 [] ++ [[] ++ [NTS A] ++ []] ++ ([NTS A; NTS n']::t')`
 by METIS_TAC [APPEND_NIL, APPEND] THEN
 `¬EXISTS ($~ o isTmnlSym) []` by METIS_TAC [EVERY_DEF, NOT_EVERY] THEN

`(([NTS A; NTS n']::t') =
 [] ++ [[] ++ [] ++ [NTS A] ++ [NTS n'] ++ []] ++ t') ∧
 ¬EXISTS ($~ o isTmnlSym) [] ∧
 ¬(∃e.MEM e [] ∧
   ∀p0 p1 nt.
   e ≠ [] ++ p0 ++ [NTS nt] ++ p1 ++ [] ∨
   EXISTS ($~ o isTmnlSym) p0)` by METIS_TAC [NOT_EVERY, EVERY_DEF, APPEND_NIL,
					      APPEND, MEM] THEN
METIS_TAC [NOT_EVERY, EVERY_DEF, APPEND_NIL,APPEND, MEM]) THEN



`LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) ≥ 2` 
by  (SRW_TAC [][distinctldNts_def, rmDupes, ldNts_def, delete_def] THEN
     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
     DECIDE_TAC) THEN
FULL_SIMP_TAC (arith_ss) [],

FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def,lreseq] THEN
SRW_TAC [][distinctldNts_def,ldNts_def,rmDupes,delete_def]]);


val ntProp = Define
`ntProp dl p' s' tsl' B' sfx' n1 n2= 
(dl = p' ++ [tsl' ++ [NTS B'] ++ sfx'] ++ [tsl'++[NTS n1;NTS n2]++sfx'] ++ s') ∧
 EVERY isTmnlSym tsl' ∧
 ((n1=B') ∨  
   ∃r1 r2 v' w'.
   (s'=r1++[(tsl' ++ v' ++ [NTS B'] ++ w' ++ sfx')]++r2) ∧ EVERY isTmnlSym v')`;

val lastExpProp = Define
`lastExpProp (g,dl,z) = 
(∃p' s' tsl' B' sfx' n1 n2.
 ntProp dl p' s' tsl' B' sfx' n1 n2 ∧
  ∃dl' dl'' dl''' v' w'.
  lderives g ⊢ dl' ◁ [NTS n1;NTS n2] → (v'++[NTS B']++w') ∧
  ∃rst.lderives g ⊢ dl'' ◁  (v'++[NTS B']++w') → (v'++rst) ∧
  ∃rst'.lderives g ⊢ dl''' ◁ sfx' → rst' ∧
  (z = tsl'++v'++rst++rst') ∧
  distElemSubset dl dl' ∧
  distElemSubset dl dl'' ∧
  distElemSubset dl dl''' ∧
  (∀e.MEM e dl' ⇒ MEM (tsl'++ e ++ sfx') dl) ∧
  (∀e.MEM e dl'' ⇒ MEM ((tsl'++v') ++ e ++sfx') dl) ∧ 
  ¬symProp dl' ∧ ¬symProp dl'' ∧ ¬(symProp (dl'++(TL dl''))))`;


val ldMemlderivesPfxSfx = store_thm
("ldMemlderivesPfxSfx",
``∀dl x1 x2.
lderives g ⊢ dl ◁ (x1++x2) → y ∧ isCnf g ∧ MEM e dl ∧
EVERY isTmnlSym x1 ∧EVERY isNonTmnlSym x2
⇒
∃p s.(e=p++s) ∧ EVERY isTmnlSym p ∧ EVERY isNonTmnlSym s``,

Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [] 
 THENL[

       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       `(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
       (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf] THEN
       `(s1=x1) ∧(x2=[NTS lhs]++s2)`by METIS_TAC [symListDiv] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`s1`,`[NTS lhs]++s2`] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],


       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       `(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
       (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf] THEN
       `(s1=x1) ∧(x2=[NTS lhs]++s2)`by METIS_TAC [symListDiv] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`s1`,`rhs++s2`] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       `(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
       (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf] 
       THENL[
	     `(s1=x1) ∧(x2=[NTS lhs]++s2)`by METIS_TAC [symListDiv] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`rhs++s2`] MP_TAC) THEN
	     SRW_TAC [][],
	     
	     FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs`,`s2`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     `(s1=x1) ∧(x2=[NTS lhs]++s2)`by METIS_TAC [symListDiv] THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     ]]);


val notSymPropTl = store_thm
("notSymPropTl",
``∀dl.dl≠[] ∧ ¬symProp dl ⇒ ¬symProp (TL dl)``,

SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][symProp] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

FIRST_X_ASSUM (Q.SPECL_THEN [`h::p`,`tsl`,`B`,`sfx`,`v`,`w`]
		 MP_TAC) THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1` THEN
SRW_TAC [][] THEN1 METIS_TAC [everyNotTwice] THEN
Q.EXISTS_TAC `s0` THEN
Q.EXISTS_TAC `s1` THEN
SRW_TAC [][] THEN1 METIS_TAC [everyNotTwice] THEN
METIS_TAC [everyNotTwice]);


val addFrontrtc2list = store_thm
("addFrontrtc2list",
``∀l.rtc2list (lderives g) l ∧ EVERY isTmnlSym rhs 
    ⇒
    rtc2list (lderives g) (MAP (addFront rhs) l)``,

Induct_on `l` THEN SRW_TAC [][addFront_def] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
METIS_TAC [lderives_same_append_left]);

val ldMemlderivesSfx = store_thm
("ldMemlderivesSfx",
``∀dl x1 x2.
lderives g ⊢ dl ◁ (x1++x2) → y ∧ isCnf g ∧
MEM (p0++rst) dl ∧ EVERY isTmnlSym p0 ∧
EVERY isTmnlSym x1 ∧EVERY isNonTmnlSym x2
⇒
∃p s.(rst=p++s) ∧ EVERY isTmnlSym p ∧ EVERY isNonTmnlSym s``,

SRW_TAC [][] THEN
`∃p s.(p0++rst = p ++ s) ∧ EVERY isTmnlSym p ∧ EVERY isNonTmnlSym s` 
 by METIS_TAC [ldMemlderivesPfxSfx] THEN
IMP_RES_TAC twoListAppEq THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_NIL,EVERY_DEF,EVERY_APPEND]);

val dropLast = Define 
`dropLast sfx l = REVERSE (DROP (LENGTH sfx) (REVERSE l))`;

val listsec = Define 
    `listsec front back l =
	     (dropLast back) ((DROP (LENGTH front)) l)`;


val listsecPfxSfx = store_thm
("listsecPfxSfx",
 ``∀m.(listsec p s (p++m++s) = m)``,
 SRW_TAC [][listsec,dropLast] THEN
 `(DROP (LENGTH p) (p ++ m ++ s)) = m++s` 
 by METIS_TAC [BUTFIRSTN_LENGTH_APPEND,APPEND_ASSOC] THEN
 ONCE_ASM_REWRITE_TAC[] THEN
 SRW_TAC [][REVERSE_APPEND] THEN
 METIS_TAC [LENGTH_REVERSE, REVERSE_REVERSE,BUTFIRSTN_LENGTH_APPEND]);
    
val listsecDropNilSfx = store_thm
("listsecDropNilSfx",
``listsec p [] (p++x) = x``,

SRW_TAC [][listsec,dropLast] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND]);

val listsecldSfxNil = store_thm
("listsecldSfxNil",
``∀dl x.
lderives g ⊢ dl ◁ (p++x) → (p++y) ∧ EVERY isTmnlSym p
⇒
lderives g ⊢ MAP (listsec p []) dl ◁ listsec p [] (p++x) → listsec p [] (p++y)``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listsecDropNilSfx] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN

(IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN1
METIS_TAC [APPEND_ASSOC,listsecDropNilSfx,APPEND_NIL,APPEND_ASSOC,APPEND,
	   EVERY_DEF,EVERY_APPEND] THEN1
METIS_TAC [APPEND_ASSOC,listsecDropNilSfx,APPEND_NIL,APPEND_ASSOC,APPEND,
	   EVERY_DEF,EVERY_APPEND]  THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`s1''=[]`  by (Cases_on `s1''` THEN SRW_TAC [][] THEN
	       Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_ASSOC,listsecDropNilSfx,APPEND_NIL,APPEND_ASSOC,APPEND,
	   EVERY_DEF,EVERY_APPEND]));

val listsecLast = store_thm
("listsecLast",
``∀l.
(LAST l =p ++ ml ++ s) ∧ (l≠[]) ∧
(∀e.MEM e l ⇒ ∃m. m ≠ [] ∧ (e = p ++ m ++ s))
⇒
(LAST (MAP (listsec p s) l) = ml)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `l=[]`THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][listsecPfxSfx] THEN1
METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
`(LAST l = p ++ ml ++ s)` by METIS_TAC [APPEND,last_append] THEN
METIS_TAC [MAP_EQ_NIL,APPEND,last_append]);


val memListDistSub = store_thm
("memListDistSub",
``∀dl dl'.(∀e.MEM e dl' ⇒ MEM (p++e++s) dl) ⇒
distElemSubset dl dl'``,

Induct_on `dl'` THEN SRW_TAC [][] THEN1
 (FULL_SIMP_TAC (srw_ss()) [distElemSubset_def] THEN
 SRW_TAC [][distinctldNts_def,ldNts_def,rmDupes]) THEN

 FULL_SIMP_TAC (srw_ss()) [distinctldNts_def,ldNts_def,distElemSubset_def,
			   FILTER_APPEND] THEN
 SRW_TAC [][] THEN
 `MEM e (FILTER isNonTmnlSym h ++
	 FILTER isNonTmnlSym (FLAT dl'))` by METIS_TAC [rmd_r2] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [MEM_FILTER] THEN
 `MEM (p++h++s) dl` by METIS_TAC [] THEN
 Q_TAC SUFF_TAC `MEM e (FILTER isNonTmnlSym (FLAT dl))` THEN1
 METIS_TAC [rmd_r2] THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
 SRW_TAC [][FILTER_APPEND,FLAT_APPEND] THEN
      METIS_TAC [MEM_APPEND,MEM,APPEND_ASSOC]) THEN
 
 FULL_SIMP_TAC (srw_ss()) [MEM_FLAT,MEM_FILTER] THEN
 `MEM (p++l++s) dl` by METIS_TAC [] THEN
 Q_TAC SUFF_TAC `MEM e (FILTER isNonTmnlSym (FLAT dl))` THEN1
 METIS_TAC [rmd_r2] THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
 SRW_TAC [][FILTER_APPEND,FLAT_APPEND] THEN
 METIS_TAC [MEM_APPEND,MEM,APPEND_ASSOC]);
      
val dldntsMemList = store_thm
("dldntsMemList",
``∀l.(MEM e (distinctldNts l) ⇒ MEM e (FLAT l))``,
Induct_on `l` THEN SRW_TAC [][distinctldNts_def,ldNts_def,rmDupes] THEN
SRW_TAC [][FILTER_APPEND] THEN
`MEM e (FILTER isNonTmnlSym (h ++ FLAT l))` by METIS_TAC [rmd_r2] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_FILTER]);




val rtc2listImpLd = store_thm
("rtc2listImpLd",
``∀t. rtc2list R t ⇒ R ⊢ t ◁ HD t → LAST t``,

Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]);

val distesubtrans = store_thm
("distesubtrans",
``distElemSubset dl dl1 ∧ distElemSubset dl1 dl0 ⇒
 distElemSubset dl dl0``,

SRW_TAC [][distElemSubset_def]);

val lastExp = store_thm
("lastExp",
``∀dl z0 pz0 sz0.
 (lderives g) ⊢ dl ◁ z0 → z ∧ isCnf g ∧ EVERY isTmnlSym z ∧
 (z0=pz0++sz0) ∧ EVERY isTmnlSym pz0 ∧ EVERY isNonTmnlSym sz0 ∧
 symProp dl
 ⇒
 lastExpProp (g,dl,z)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

 (FULL_SIMP_TAC (srw_ss()) [lderives_def, lastExpProp, listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [symProp] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`sz0 = []` by
(Cases_on `sz0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def]) THEN
`pz0 = tsl` by METIS_TAC [symListDiv] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_ASSOC, APPEND_11, APPEND, NOT_CONS_NIL]) THEN

IMP_RES_TAC listDerivHdBrk THEN
`∃pz0' sz0'.(h' = pz0' ++ sz0') ∧ EVERY isTmnlSym pz0' ∧ EVERY isNonTmnlSym sz0'`
 by METIS_TAC [ldMemlderivesPfxSfx, MEM] THEN
SRW_TAC [][] THEN
Cases_on `symProp ((pz0' ++ sz0')::t)` THEN1
(`lastExpProp (g,(pz0' ++ sz0')::t,z)` by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [lastExpProp] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ntProp] THEN SRW_TAC [][] THEN1
 
(MAP_EVERY Q.EXISTS_TAC [`h::p'`,`s'`,`tsl'`,`B'`,`sfx'`, `B'`,`n2`] THEN
 SRW_TAC [][] THEN
 MAP_EVERY Q.EXISTS_TAC [`dl'`,`dl''`,`dl'''`,`v'`,`w'`] THEN SRW_TAC [][] THEN
 Q.EXISTS_TAC `rst` THEN SRW_TAC [][] THEN
 METIS_TAC [distesubaddlist, APPEND_NIL, APPEND]) THEN
 
 MAP_EVERY Q.EXISTS_TAC [`h::p'`,
			`r1 ++[tsl' ++ v'' ++ [NTS B'] ++ w'' ++ sfx'] ++ r2`,
			 `tsl'`,`B'`,`sfx'`, `n1`,`n2`] THEN
 SRW_TAC [][] THEN1
 METIS_TAC [] THEN
 MAP_EVERY Q.EXISTS_TAC [`dl'`,`dl''`,`dl'''`,`v'`,`w'`] THEN SRW_TAC [][] THEN
 Q.EXISTS_TAC `rst` THEN SRW_TAC [][] THEN
 METIS_TAC [distesubaddlist, APPEND_NIL, APPEND, APPEND_ASSOC]) THEN

(* ¬symProp ((pz0' ++ sz0')::t) *)

FULL_SIMP_TAC (srw_ss()) [symProp] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1

(* p = [] *)
(Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1

(* s0 = [] *)
(`EVERY isTmnlSym (tsl ++ v)`by METIS_TAC [EVERY_APPEND] THEN
`(pz0' = tsl ++ v) ∧ (sz0' = [NTS B]++w++sfx)`
by METIS_TAC [symListDiv, APPEND_ASSOC] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
`EVERY isNonTmnlSym [NTS lhs]` by SRW_TAC [][isNonTmnlSym_def] THEN
`(s1'=tsl) ∧ ([NTS lhs]++s2 = [NTS B]++sfx)`
by METIS_TAC [NOT_CONS_NIL, symlistdiv3]  THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
`rhs = v ++ [NTS B]++w` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
SRW_TAC [][] THEN
`((LENGTH (v++[NTS B]++w) = 2) ∧ EVERY isNonTmnlSym (v++[NTS B]++w)) ∨
(LENGTH (v++[NTS B]++w) = 1) ∧ EVERY isTmnlSym (v++[NTS B]++w)` 
by METIS_TAC [isCnf] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
(* nonTmnl rule*)
`v=[]` by
(Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def]) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH w = 1` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
Cases_on `e` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp, ntProp] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`, `s1`,`s1'`,`B`,`s2`,`B`,`n`] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN

`EVERY isNonTmnlSym ([NTS B] ++ [NTS n] ++ s2)` 
by FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, EVERY_APPEND] THEN
`¬symProp ((s1' ++ [NTS B] ++ [NTS n] ++ s2)::s1)` 
by MAGIC (*METIS_TAC [symProp, NOT_EVERY]*) THEN

`∃dl1 dl2 x y. splitDerivProp (g,(s1' ++ [NTS B] ++ [NTS n] ++ s2)::s1,z)
 (dl1,s1'++[NTS B]++[NTS n],x) (dl2,s2,y)` 
by METIS_TAC [ldSplitDeriv,APPEND_ASSOC,HD] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN 
SRW_TAC [][] THEN
`EVERY isNonTmnlSym ([NTS B]++[NTS n])` by SRW_TAC [][isNonTmnlSym_def] THEN
`∃dl3 dl4 x' y'. splitDerivProp (g,dl1,x)
 (dl3,s1',x') (dl4,[NTS B]++[NTS n],y')` by METIS_TAC [ldSplitDeriv,
						       APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`[[NTS B;NTS n]]`,`dl4`,`dl2`,`[]`,`[NTS n]`] THEN
SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Q.EXISTS_TAC `y'` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `y` THEN SRW_TAC [][] THEN1

(* 0 *)
(Cases_on `dl3` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
 SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN1

(* 1 *)
(FULL_SIMP_TAC (srw_ss()) [distElemSubset_def] THEN
 SRW_TAC [][] THEN
IMP_RES_TAC dldntsMemList THEN
 SRW_TAC [][distinctldNts_def,ldNts_def, FILTER_APPEND] THEN
Cases_on `dl3` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 FULL_SIMP_TAC (srw_ss()) [addLast_def, FILTER_APPEND] THEN
METIS_TAC [rmd_r2, rgr_r9eq, MEM, MEM_APPEND, APPEND]) THEN1

(* 2 *)
 METIS_TAC [distesubtrans,distesubaddlist,APPEND,APPEND_NIL, distesub1,
	    memListDistSub] THEN1

(* 3 *)
 METIS_TAC [distesubtrans,distesubaddlist,APPEND,APPEND_NIL, distesub2] THEN1

(* 4 *)
METIS_TAC [APPEND, APPEND_ASSOC] THEN1

(* 5 *)
(Cases_on `dl4` THEN
 Cases_on `dl3` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN1
 METIS_TAC [APPEND_ASSOC, APPEND, APPEND_11] THEN
Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [addFront_def, addLast_def] THEN
MAGIC) THEN1

(* 6 *)
(FULL_SIMP_TAC (srw_ss()) [symProp] THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN  SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [lreseq] THEN  SRW_TAC [][] THEN METIS_TAC [MEM]) THEN

(* 7 *)
Cases_on `dl4` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]) THEN

(* s0 ≠ [] *)
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
`EVERY isNonTmnlSym [NTS lhs]` by SRW_TAC [][isNonTmnlSym_def] THEN
`(s1'=tsl) ∧([NTS lhs]++s2 = [NTS B]++sfx)` by METIS_TAC [symlistdiv3, 
							  NOT_CONS_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
`((LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs) ∨
(LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` 
by METIS_TAC [isCnf] THEN1
(* nonTmnl rule*)

(FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
Cases_on `e1` THEN Cases_on `e2` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp, ntProp] THEN
`(s1' = pz0') ∧ ([NTS n;NTS n']++s2 = sz0')` by METIS_TAC [symListDiv, APPEND,
							   APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`, `(t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1)`,
			`pz0'`,`B`,`s2`,`n`,`n'`] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN

`EVERY isNonTmnlSym ([NTS n] ++ [NTS n'] ++ s2)` 
by FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, EVERY_APPEND] THEN
`(pz0' ++ NTS n::NTS n'::s2 = (pz0' ++ [NTS n] ++ [NTS n']) ++ s2)`
by METIS_TAC [APPEND, APPEND_ASSOC] THEN
`¬symProp ((pz0' ++ NTS n::NTS n'::s2)::
(t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1))` by MAGIC THEN
`∃dl1 dl2 x y. splitDerivProp (g,(pz0' ++ NTS n::NTS n'::s2)::
			       (t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1),z)
(dl1,pz0'++[NTS n]++[NTS n'],x) (dl2,s2,y)` 
by METIS_TAC [ldSplitDeriv] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN

(*list sec *)
MAGIC) THEN

FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
Cases_on `e` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`∃p0 p1 nt.s1'++[TS t]++s2 = s1' ++ p0 ++ [NTS nt] ++ p1 ++ s2`
by METIS_TAC [] THEN
`[TS t] = p0++[NTS nt]++p1` by METIS_TAC [APPEND_ASSOC, APPEND_11]THEN
FULL_SIMP_TAC (srw_ss()) [lreseq]) THEN

FIRST_X_ASSUM (Q.SPECL_THEN [`t'`,`tsl`,`B`,`sfx`,`v`,`w`,
			     `s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`]
	       MP_TAC) THEN 
SRW_TAC [][] THEN
METIS_TAC [NOT_EVERY]);



val inpLeninv = store_thm
("inpLeninv",
 ``LENGTH z > 2**(k - 1) ∧ EVERY isTmnlSym z ∧
 (lderives g) ⊢ dl ◁ [NTS A] → z ∧ (k = LENGTH (distinctldNts dl)) ∧
 isCnf g 
 ⇒
 symProp dl``,
 
 SRW_TAC [][] THEN
Q.ABBREV_TAC `k = LENGTH (distinctldNts dl)` THEN
`¬(LENGTH z ≤ 2 ** (k − 1))` by DECIDE_TAC THEN
METIS_TAC [inpLen]);



val flatRepSuc = store_thm
("flatRepSuc",
``∀p i.FLAT (lpow p (SUC i)) = p++FLAT (lpow p i)``,

Induct_on `i` THEN SRW_TAC [][] THEN
SRW_TAC [][lpow, REPLICATE] THEN
`1=SUC 0`by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][REPLICATE]);


val flatRepComm = store_thm
("flatRepComm",
``∀i p.p++FLAT (lpow p i) =  FLAT (lpow p i)++p``,

Induct_on `i` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lpow,REPLICATE]);


val islpowTmnl = store_thm
("islpowTmnl",
``∀l.EVERY isTmnlSym l ⇒ EVERY isTmnlSym (FLAT (lpow l i))``,

Induct_on `i` THEN SRW_TAC [][lpow,REPLICATE] THEN
FULL_SIMP_TAC (srw_ss()) [lpow,REPLICATE]);


val rtcDerivesReplEnd = store_thm
("rtcDerivesReplEnd",
 ``∀i.(lderives g)^* [NTS B] (p ++ [NTS B] ++ s) ∧
 EVERY isTmnlSym p ∧
 (lderives g)^*  [NTS B] z ∧ EVERY isTmnlSym z ∧
 (lderives g)^* s z' ∧ EVERY isTmnlSym z'
  ⇒
  (lderives g)^* [NTS B] (FLAT (lpow p i) ++ z ++ FLAT (lpow z' i))``,

Induct_on `i` THEN SRW_TAC [][] THEN1
(SRW_TAC [][lpow,REPLICATE] THEN
 METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	    APPEND_ASSOC,RTC_RTC]) THEN
RES_TAC THEN
SRW_TAC [][flatRepSuc] THEN
Q_TAC SUFF_TAC
`(lderives g)^* [NTS B] (p ++ FLAT (lpow p i) ++ z ++  FLAT (lpow z' i) ++z')` THEN1
METIS_TAC [flatRepComm,APPEND_ASSOC] THEN
`(lderives g)^* (p++[NTS B]++s) (p++FLAT (lpow p i) ++ z ++ FLAT (lpow z' i)++s)` by
METIS_TAC [rtc_lderives_same_append_right,rtc_lderives_same_append_left,
	   APPEND_ASSOC] THEN
`EVERY isTmnlSym (p ++ FLAT (lpow p i) ++ z ++ FLAT (lpow z' i))` 
 by METIS_TAC [islpowTmnl,EVERY_APPEND] THEN
METIS_TAC [RTC_RTC,rtc_lderives_same_append_left]);


val ntlist = Define
`ntlist g = nonTerminalsList (startSym g) (rules g)`;



val numdlds = store_thm
("numdlds",
``lderives g ⊢ dl ◁ [NTS (startSym g)] → z ⇒ LENGTH (distinctldNts dl) ≥ 1``,

SRW_TAC [][llanguage_def] THEN
FULL_SIMP_TAC (srw_ss()) [distinctldNts_def, ldNts_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][isNonTmnlSym_def, rmDupes] THEN
DECIDE_TAC);


val listderivTrans = store_thm
("listderivTrans",
``∀dl1 dl2 x y.R ⊢ dl1 ◁ x → y ∧ R ⊢ dl2 ◁ y → z 
⇒
R ⊢ dl1 ++ TL dl2 ◁ x → z``,

Induct_on `dl1` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl2` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl1=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'::t`] MP_TAC) THEN SRW_TAC [][] THEN
Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) []);


val addFrontListsec = store_thm
("addFrontListsec",
``∀t.(∀e.MEM e t ⇒ ∃rst.(e=s1++rst)) ⇒ 
 (MAP (addFront s1) (MAP (listsec s1 []) t) = t)``,

Induct_on `t` THEN SRW_TAC [][addFront_def, listsec, dropLast] THEN
`∃rst.h = s1++rst` by METIS_TAC [] THEN
SRW_TAC [][] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND]);

val notspropLsTmnls = store_thm
("notspropLsTmnls",
``∀dl v rst.¬symProp dl ∧ lderives g ⊢ dl ◁ (v ++ rst) → (v ++ rst') ∧
EVERY isTmnlSym (v++rst') ⇒
¬symProp (MAP (listsec v []) dl)``,

Induct_on `dl` THEN SRW_TAC [][] THEN
`¬symProp dl` by METIS_TAC [TL, NOT_CONS_NIL, spropApp] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(FULL_SIMP_TAC (srw_ss()) [symProp, listderiv_def] THEN
SRW_TAC [][listsec, dropLast] THEN
`rst = rst'` by METIS_TAC [APPEND_11] THEN
SRW_TAC [][BUTFIRSTN_LENGTH_APPEND] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq]) THEN


IMP_RES_TAC listDerivHdBrk THEN
`h = v ++ rst` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN1

(IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN1

 (FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`rhs++s2`] MP_TAC) THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [symProp] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
  
FULL_SIMP_TAC (srw_ss()) [listsec, dropLast] THEN
`DROP (LENGTH s1) (s1 ++ [NTS lhs] ++ s2) = [NTS lhs]++s2` 
  by METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND_ASSOC] THEN
`DROP (LENGTH s1) (s1 ++ rhs++s2) = rhs++s2` 
  by METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND_ASSOC] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1

(`tsl = []` by (Cases_on `tsl` THEN SRW_TAC [][] THEN Cases_on `h` THEN
	       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`MAP (addFront s1) ((rhs ++ s2)::MAP (listsec s1 []) t) =
MAP (addFront s1)  (s0 ++ [v ++ [NTS B] ++ w ++ s2] ++ s1')`
  by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
`∀e.MEM e t ⇒ ∃rst.(e=s1++rst)` by MAGIC THEN
`MAP (addFront s1) (MAP (listsec s1 []) t)  = t`by METIS_TAC [addFrontListsec] THEN
SRW_TAC [][] THEN
`(s1 ++ [NTS B] ++ s2)::(s1 ++ rhs ++ s2)::t =
[] ++ [s1 ++ [NTS B] ++ s2] ++ 
(MAP (addFront s1) s0 ++ [s1 ++ v ++ [NTS B] ++ w ++ s2] ++ MAP (addFront s1) s1')`
by METIS_TAC [APPEND_ASSOC, APPEND_NIL, APPEND] THEN
`¬EXISTS ($~ o isTmnlSym) s1` by METIS_TAC [NOT_EVERY] THEN
`¬EXISTS ($~ o isTmnlSym) v` by METIS_TAC [NOT_EVERY, everyNotTwice] THEN
`∀e.MEM e (MAP (addFront s1) s0) ⇒
∃p0 p1 nt.(e = s1 ++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧ EVERY ($~ o $~ o isTmnlSym) p0`
by MAGIC (*METIS_TAC [leftmostAddFront', APPEND_ASSOC]*) THEN
MAGIC (* METIS_TAC [NOT_EVERY, APPEND_ASSOC] *)) THEN

`MAP (addFront s1) ((rhs ++ s2)::MAP (listsec s1 []) t) =
MAP (addFront s1)  (t' ++ [tsl ++ [NTS B] ++ sfx] ++ s0 ++
		    [tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1')`
by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
`∀e.MEM e t ⇒ ∃rst.(e=s1++rst)` by MAGIC THEN
`MAP (addFront s1) (MAP (listsec s1 []) t)  = t`by METIS_TAC [addFrontListsec] THEN
SRW_TAC [][] THEN
`(s1 ++ [NTS lhs] ++ s2)::(s1 ++ rhs ++ s2)::t =
([s1++[NTS lhs]++s2] ++ MAP (addFront s1) t') ++
[(s1 ++ tsl) ++ [NTS B] ++ sfx] ++
(MAP (addFront s1) s0 ++ [s1 ++ tsl ++ v ++ [NTS B] ++ w ++ sfx] ++
MAP (addFront s1) s1')`
by METIS_TAC [APPEND_ASSOC, APPEND_NIL, APPEND] THEN
`¬EXISTS ($~ o isTmnlSym) (s1++tsl)` by METIS_TAC [NOT_EVERY,EVERY_APPEND,
						   everyNotTwice] THEN
`¬EXISTS ($~ o isTmnlSym) v` by METIS_TAC [NOT_EVERY, everyNotTwice] THEN
`∀e.MEM e (MAP (addFront s1) s0) ⇒
∃p0 p1 nt.(e = s1 ++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧ EVERY ($~ o $~ o isTmnlSym) p0`
by MAGIC (*METIS_TAC [leftmostAddFront', APPEND_ASSOC]*) THEN
MAGIC (* METIS_TAC [NOT_EVERY, APPEND_ASSOC] *)) THEN1


FIRST_X_ASSUM (Q.SPECL_THEN [`v`,`s1''++rhs++s2`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [symProp] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
  
FULL_SIMP_TAC (srw_ss()) [listsec, dropLast] THEN
`DROP (LENGTH v) (v ++ s1'' ++ [NTS lhs] ++ s2) = s1''++[NTS lhs]++s2` 
  by METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND_ASSOC] THEN
`DROP (LENGTH v) (v++ s1'' ++ rhs++s2) = s1''++rhs++s2` 
  by METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND_ASSOC] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAGIC,

 Cases_on `s1''` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN1

(`s1'=[NTS lhs]` by METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [symProp] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listsec, dropLast] THEN
`DROP (LENGTH s1) (s1 ++ [NTS lhs] ++ s2) = [NTS lhs]++s2` 
  by METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND_ASSOC] THEN
`DROP (LENGTH s1) (s1 ++ rhs++s2) = rhs++s2` 
  by METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND_ASSOC] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAGIC) THEN

 Cases_on `h` THEN SRW_TAC [][] THEN 
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]));



val pumpCfg = store_thm
("pumpCfg",
``∀z.z ∈ (llanguage g)  ∧ isCnf (g:('a,'b) grammar)  ∧ 
 EVERY (gaw g) (ntList g) ⇒
 ∃n.LENGTH z ≥ n ⇒
 ∃u v w x y.
 LENGTH v + LENGTH x ≥ 1 ∧
 LENGTH v + LENGTH w + LENGTH x ≤ n ∧
 ∀i.i ≥ 0 ⇒ (u++FLAT (lpow v i)++w++FLAT (lpow x i)++y) ∈ (language g)``,

SRW_TAC [][] THEN
 `(lderives g)^* [NTS (startSym g)] z ∧ EVERY isTmnlSym z` 
 by FULL_SIMP_TAC (srw_ss()) [llanguage_def] THEN
 `∃dl.(lderives g) ⊢ dl ◁ [NTS (startSym g)] → z` 
 by METIS_TAC [rtc2list_exists'] THEN
 Q.ABBREV_TAC `k=LENGTH (distinctldNts dl)` THEN
Q.EXISTS_TAC `2**k` THEN
SRW_TAC [][] THEN
`LENGTH (distinctldNts dl) ≥ 1` by METIS_TAC [numdlds] THEN
`k ≥ 1 ⇒ 1 ≤ k` by DECIDE_TAC THEN
 `1 ≤ k` by METIS_TAC [] THEN
 `LENGTH z > 2**(k-1)` by METIS_TAC [powGt] THEN
 `symProp dl` by METIS_TAC [inpLeninv,symProp] THEN
`EVERY isNonTmnlSym ([NTS (startSym g)]:('a,'b) symbol list)`
by METIS_TAC [APPEND_ASSOC,APPEND_11,symbol_11,isNonTmnlSym_def,EVERY_DEF] THEN
 `∃pz0:('a,'b) symbol list sz0:('a,'b) symbol list.([NTS (startSym g)]=pz0++sz0) ∧ 
	 EVERY isTmnlSym pz0 ∧ EVERY isNonTmnlSym sz0`
 by METIS_TAC [EVERY_DEF,APPEND_NIL] THEN
`lastExpProp (g,dl,z)` 
by METIS_TAC [lastExp,symbol_11] THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp] THEN
SRW_TAC [][] THEN
`lderives g ⊢ (dl'++TL dl'') ◁ [NTS n1]++[NTS n2] → (v'++rst)` by 
METIS_TAC [listderivTrans, APPEND] THEN
`∃pfx sfx.([NTS n1]++[NTS n2]=pfx++sfx) ∧ EVERY isTmnlSym pfx ∧
	 EVERY isNonTmnlSym sfx` by
(MAP_EVERY Q.EXISTS_TAC [`[]`,`[NTS n1]++[NTS n2]`] THEN
 SRW_TAC [][isNonTmnlSym_def]) THEN
`∃dl1 dl2 zb zy.
   splitDerivProp (g,dl'++TL dl'',v'++rst) 
   (dl1,[NTS n1],zb) (dl2,[NTS n2],zy)` by METIS_TAC [ldSplitDeriv,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
`LENGTH zb ≤ 2**(LENGTH (distinctldNts dl1) -1)`
by METIS_TAC [symProp, inpLen,EVERY_APPEND] THEN
`LENGTH zy ≤ 2**(LENGTH (distinctldNts dl2) -1)`
by METIS_TAC [symProp, inpLen,EVERY_APPEND] THEN
SRW_TAC [][] THEN
`∃v''.zb++zy=v'++v''`by 
(IMP_RES_TAC twoListAppEq THEN 
 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
 METIS_TAC [APPEND_ASSOC]) THEN
SRW_TAC [][] THEN
`lderives g ⊢ MAP (listsec v' []) dl'' ◁
   listsec v' [] (v' ++ ([NTS B']++w')) → listsec v' [] (v' ++ v'')`
by METIS_TAC [listsecldSfxNil,APPEND_ASSOC,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [listsecDropNilSfx] THEN
`¬symProp (MAP (listsec v' []) dl'')` by METIS_TAC [notspropLsTmnls,
						    APPEND_ASSOC,
						    EVERY_APPEND] THEN


`MEM (v'++[NTS B']++w') dl'` by 
(Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 METIS_TAC [MEM, MEM_APPEND, APPEND_FRONT_LAST]) THEN
`v' ++ [NTS B'] ++ w' = v' ++ ([NTS B']++w')` by SRW_TAC [][] THEN
`∃p1 p2.([NTS B']++w' = p1++p2) ∧ EVERY isTmnlSym p1 ∧ EVERY isNonTmnlSym p2`
by METIS_TAC [ldMemlderivesSfx] THEN
`∃dl1 dl2 zb' zy'.
   splitDerivProp (g,(MAP (listsec v' []) dl''),v'') (dl1,[NTS B'],zb') (dl2,w',zy')`
by METIS_TAC [APPEND,ldSplitDeriv] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`tsl'`,`v'`,`zb'`,`zy'`,`rst'`] THEN
SRW_TAC [][] 
THENL[
      `MEM (NTS B') (ldNts (TL dl'))` by MAGIC THEN
      `v'≠[] ∨ w'≠[]` by MAGIC THEN1
      (`LENGTH v' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
       DECIDE_TAC) THEN
      `zy' ≠ []` by MAGIC THEN
      `LENGTH zy' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
       DECIDE_TAC,

       `LENGTH (zb ++ zy) = LENGTH (v' ++ zb' ++ zy')`
       by METIS_TAC [APPEND_ASSOC] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `LENGTH (distinctldNts dl1) ≤ k` by MAGIC THEN
       `LENGTH (distinctldNts dl2) ≤ k` by MAGIC THEN
       `LENGTH zb ≤ 2 ** (k-1)` by METIS_TAC [powLe] THEN
       `LENGTH zy ≤ 2 ** (k-1)` by METIS_TAC [powLe] THEN
       `LENGTH zb + LENGTH zy ≤ 2**(k-1) + 2**(k-1)`by DECIDE_TAC THEN
       `LENGTH zb + LENGTH zy ≤ 2*2**(k-1)`by DECIDE_TAC THEN
       `LENGTH zb + LENGTH zy ≤ 2**(k-1+1)`by METIS_TAC [powMult] THEN
       `k ≥ 1` by MAGIC THEN
       FULL_SIMP_TAC (arith_ss) [],

       MAGIC
       ]);

val _ = export_theory();

