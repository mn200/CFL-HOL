open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory


open listLemmasTheory relationLemmasTheory grammarDefTheory
     arithmeticLemmasTheory symbolDefTheory cnfTheory

val _ = new_theory "pumpingLemma";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1
val _ = diminish_srw_ss ["list EQ"];


val cnfvwNotNil = store_thm
("cnfvwNotNil",
``∀dl x. lderives g ⊢ dl ◁ x → (v ++ [NTS B] ++ w) ∧ isCnf g ∧ LENGTH x > 1 ⇒
	     (v ≠ [] ∨ w≠ [])``,

Induct_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl` THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][] THEN1

(FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 Cases_on `v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `w` THEN FULL_SIMP_TAC (srw_ss()) []) THEN

FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
	     (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (arith_ss) []);

val cnfNotLderivesNil = store_thm
("cnfNotLderivesNil",
``∀dl x.lderives g ⊢ dl ◁ x → y ∧ isCnf g ∧ LENGTH dl > 1 ⇒ y ≠ []``,

Induct_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
`(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
	     (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf_def] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (arith_ss) []  THEN
METIS_TAC [LENGTH_NIL, DECIDE ``0 ≠ 2``, DECIDE ``0 ≠ 1``]);


val cnfNotLderivesNilAllntms = store_thm
("cnfNotLderivesNilAllntms",
``∀dl x pz0 sz0.lderives g ⊢ dl ◁ x → y ∧ isCnf g  ∧ sz0 ≠ [] ∧
(x = pz0 ++ sz0) ∧ EVERY isTmnlSym pz0 ∧ EVERY isNonTmnlSym sz0
⇒ y ≠ []``,

Induct_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
 `(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
 (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf_def]
 THENL[
       METIS_TAC [LENGTH_NIL, DECIDE ``0 ≠ 2``, DECIDE ``0 ≠ 1``],
       METIS_TAC [LENGTH_NIL, DECIDE ``0 ≠ 2``, DECIDE ``0 ≠ 1``],

       FIRST_X_ASSUM (Q.SPECL_THEN [`s1'`,`[NTS lhs']++s2'`] MP_TAC) THEN
       SRW_TAC [][] THEN
       `rhs ≠ []` by METIS_TAC [LENGTH_NIL, DECIDE ``2 ≠ 0``] THEN
       `(s1' = s1) ∧ (rhs++s2 = [NTS lhs']++s2')` by METIS_TAC [symlistdiv3] THEN
       SRW_TAC [][] THEN
       `(s1 = pz0) ∧ ([NTS lhs]++s2 = sz0)`by METIS_TAC [symListDiv] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [EVERY_APPEND, isNonTmnlSym_def, symbol_11, APPEND_11,
		  APPEND_ASSOC],

       `(s1 = pz0) ∧ ([NTS lhs]++s2 = sz0)`by METIS_TAC [symListDiv] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN

       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
       THENL[

       `EVERY isTmnlSym (s1'++[NTS lhs'])` by METIS_TAC [EVERY_APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

       `EVERY isTmnlSym (s1'++[NTS lhs']++s1'')` by METIS_TAC [EVERY_APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) []
       THENL[

	     FIRST_X_ASSUM (Q.SPECL_THEN [`pz0++rhs`,`[NTS lhs']++s2'`] MP_TAC) THEN
	     SRW_TAC [][],

	     FIRST_X_ASSUM (Q.SPECL_THEN [`pz0++rhs`,`s1''++[NTS lhs']++s2'`] MP_TAC) THEN
	     SRW_TAC [][],

	     Cases_on `s1''` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

	     (FIRST_X_ASSUM (Q.SPECL_THEN [`s1'`,`s1++s2'`] MP_TAC) THEN
	     SRW_TAC [][]) THEN
	     SRW_TAC [][] THEN
	     `EVERY isTmnlSym (s1'++[NTS lhs'])` by METIS_TAC [EVERY_APPEND] THEN
	     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
	     ]]]);


val cnfRtcdPfxSfx = store_thm
("cnfRtcdPfxSfx",
``∀dl z z'.
     (lderives g) ⊢ dl ◁ z → z' ∧
     isCnf g ∧
     MEM (NTS B) (ldNts (TL dl)) ∧ MEM  (v++[NTS B]++x) (TL dl)
 ⇒
(v≠[]) ∨ (x≠[])``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [lderives_def, isCnf_def] THEN
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
       (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf_def] THEN
       `(s1=x1) ∧(x2=[NTS lhs]++s2)`by METIS_TAC [symListDiv] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`s1`,`[NTS lhs]++s2`] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],


       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       `(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
       (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf_def] THEN
       `(s1=x1) ∧(x2=[NTS lhs]++s2)`by METIS_TAC [symListDiv] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`s1`,`rhs++s2`] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       `(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
       (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs` by METIS_TAC [isCnf_def]
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

FOO;

val symPropExistsGen1Sym = store_thm
("symPropExistsGen1Sym",
``∀dl h y p s.
       lderives g ⊢ dl ◁ [h] → y ∧ MEM (p ++ [h] ++ s) (TL dl) ∧ isWord p
       ⇒
       symRepProp dl``,
HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [][SNOC_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl=[]` THEN
SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 `h'=[h]` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]
THENL[
      FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`LAST ([h]::t)`,`p`,`s`] MP_TAC) THEN
      SRW_TAC [][] THEN
      METIS_TAC [spropAppFst, APPEND, NOT_CONS_NIL, APPEND_ASSOC],

      FULL_SIMP_TAC (srw_ss()) [lderives_def, lreseq] THEN
      SRW_TAC [][] THEN
      Cases_on `h` THEN1

      (SRW_TAC [][symRepProp_def] THEN
       MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`n`,`[]`,`p`,`s`,
			       `t ++ [p ++ [NTS n] ++ s]`] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`t`,`[]`] THEN
       SRW_TAC [][] THEN
       Cases_on `isWord e` THEN1
       (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, listderiv_def] THEN
       SRW_TAC [][] THEN
       `rtc2list (lderives g) ([e] ++ r2')`
       by METIS_TAC [APPEND, APPEND_ASSOC, rtc2list_distrib_append_snd,
		     MEM] THEN
       `r2'=[]`by METIS_TAC [NOT_CONS_NIL, APPEND,rtc2listRtcldTmnls] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `isWord (s1 ++ [NTS lhs] ++ s2)` by METIS_TAC [last_elem, APPEND, APPEND_NIL,
						      APPEND_ASSOC] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       METIS_TAC [leftnt]) THEN

      FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
      `isWord [TS t']`by SRW_TAC [][isTmnlSym_def] THEN
      METIS_TAC [rtc2listRtcldTmnls, MEM, MEM_APPEND]
]);


val symRepPropAddLast = store_thm
("symRepPropAddLast",
 ``∀dl.symRepProp dl ⇒ symRepProp (MAP (λl.l++e) dl)``,

SRW_TAC [][symRepProp_def]  THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`MAP (λl. l ++ e) p`,`tsl`,`B`,`sfx++e`,`v`,`w`,
			     `MAP (λl. l ++ e) s0 ++
			     [tsl ++ v ++ [NTS B] ++ w ++ sfx ++ e] ++
			     MAP (λl. l ++ e) s1`] MP_TAC) THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (λl. l ++ e) s0`,`MAP (λl. l ++ e) s1`] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
SRW_TAC [][] THEN
METIS_TAC [existsThrice, NOT_EVERY, APPEND_ASSOC, APPEND_11]);

val symRepPropAddFront = store_thm
("symRepPropAddFront",
 ``∀dl.symRepProp dl ∧ EVERY isTmnlSym x ⇒
 symRepProp (MAP (addFront x) dl)``,

SRW_TAC [][symRepProp_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`MAP (addFront x) p`,`x++tsl`,`B`,`sfx`,`v`,`w`,
			     `MAP (addFront x) s0 ++
			     [x ++ tsl ++ v ++ [NTS B] ++ w ++ sfx] ++
			     MAP (addFront x) s1`] MP_TAC) THEN SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (addFront x) s0`,`MAP (addFront x) s1`] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [addFront_def, MEM_MAP] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_ASSOC, EVERY_APPEND, existsThrice, APPEND_11, NOT_EVERY]);


val symPropExistsGen0 = store_thm
("symPropExistsGen0",
``∀dl x y p s.
lderives g ⊢ dl ◁ x → y ∧ MEM (p ++ x ++ s) (TL dl) ∧ isWord p ∧ isWord y
⇒ symRepProp dl``,

Induct_on `x` THEN SRW_TAC [][] THEN1
 (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def]) THEN

`h::x = [h]++x` by METIS_TAC [APPEND] THEN
`∃dl1 dl2 y1 y2.
           lderives g ⊢ dl1 ◁ [h] → y1 ∧
           lderives g ⊢ dl2 ◁ x → y2 ∧ (y = y1 ++ y2) ∧
           (dl =
            MAP (λl. addLast l x) dl1 ++
            MAP (addFront y1) (TL dl2))`
 by METIS_TAC [ldStreams] THEN
SRW_TAC [][] THEN
Cases_on `dl1` THEN1
 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
 `h'=[h]` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [MEM_MAP, addLast_def] THEN
      `∃rst.l=p++h::rst` by
      (IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN1
       (IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
	THENL[
	      `LENGTH (h::(s1' ++ s)) = LENGTH s1'` by METIS_TAC [] THEN
	      FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],
	      `LENGTH (h::(s1'' ++ s2' ++ s)) = LENGTH s2'` by METIS_TAC [] THEN
	      FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],
	      Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      `LENGTH (h::(s1' ++ s)) = LENGTH s1'` by METIS_TAC [] THEN
	      FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
	      ]) THEN
       METIS_TAC [APPEND, APPEND_ASSOC]) THEN
      SRW_TAC [][] THEN
      `x++s = rst++x` by METIS_TAC [APPEND_ASSOC, APPEND_11, APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      `symRepProp ([h]::t)` by METIS_TAC [APPEND, APPEND_ASSOC, symPropExistsGen1Sym,
					  TL] THEN
      `symRepProp (MAP (λl'. l' ++ x) ([h]::t))` by METIS_TAC [symRepPropAddLast] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [spropAppFst, APPEND, NOT_CONS_NIL, APPEND_ASSOC],


      FULL_SIMP_TAC (srw_ss()) [MEM_MAP, addFront_def] THEN
      Cases_on `h`
      THENL[
	    Cases_on `isWord y` THEN1
	    (`isWord (p ++ NTS n::x ++ s)`by METIS_TAC [EVERY_APPEND] THEN
	     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
	    IMP_RES_TAC leftnt THEN
	    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	    `p ++ [NTS n] ++ (x ++ s) = (y1 ++ l1) ++ [NTS n'] ++ l2`
	    by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	    `EVERY isNonTmnlSym [NTS n]` by SRW_TAC [][isNonTmnlSym_def] THEN
	    `isWord (y1++l1)`by SRW_TAC [][] THEN
	    `(p = y1++l1) ∧ ([NTS n]++(x++s) = [NTS n']++l2)`
	    by METIS_TAC [MEM, symlistdiv3] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    `∃tl.MEM (l1 ++ tl ++ (x ++ s)) (TL dl2) ∧ isWord tl`
	    by
	    (FULL_SIMP_TAC (srw_ss()) [listderiv_def, rgr_r9eq] THEN
	     SRW_TAC [][] THEN
	     Cases_on `dl2` THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `h::t' = ([h]++r1) ++ [l1 ++ [NTS n] ++ (h ++ s)] ++ r2`
	     by METIS_TAC [APPEND_ASSOC, APPEND] THEN
	     `¬isWord [NTS n]` by SRW_TAC [][isTmnlSym_def] THEN
	     `∃r1' r2' tl.(r2 = r1' ++ [l1 ++ tl ++ (h++s)] ++ r2') ∧ isWord tl`
	     by METIS_TAC [rtc2listldFstNt'] THEN
	     METIS_TAC [APPEND, APPEND_ASSOC]) THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`dl2`,`y2`,`l1++tl`,`s`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `symRepProp (MAP (addFront y1) dl2)`
	    by METIS_TAC [EVERY_DEF, symRepPropAddFront, APPEND_ASSOC] THEN
	    `LAST ([NTS n]::t) = y1` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 	    `addLast [NTS n] x::MAP (λl. addLast l x) t =
              MAP (λl. addLast l x) ([NTS n]::t) ` by SRW_TAC [][] THEN
	    `MAP (λl. addLast l x) ([NTS n]::t) =
	      MAP (λl. addLast l x) (FRONT ([NTS n]::t) ++ [LAST ([NTS n]::t)])`
	    by METIS_TAC [APPEND_FRONT_LAST, MEM] THEN
	    `dl2 = x::TL dl2` by (Cases_on `dl2` THEN
				  FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	    `symRepProp (MAP (addFront (LAST ([NTS n]::t))) (x::TL dl2))`
	    by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
	    `((NTS n::x)::(MAP (λl. l ++ x) t ++
			   MAP (addFront (LAST ([NTS n]::t))) (TL dl2)))
	      = MAP (λl. l ++ x) (FRONT ([NTS n]::t)) ++
	      ((LAST ([NTS n]::t) ++ x)::
                  MAP (addFront (LAST ([NTS n]::t))) (TL dl2))`
	    by METIS_TAC [APPEND, APPEND_ASSOC] THEN
 	    METIS_TAC [spropAppSnd, MEM],

	    `t=[]` by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		       `EVERY isTmnlSym [TS t']` by SRW_TAC [][isTmnlSym_def] THEN
		       METIS_TAC [rtc2listRtcldTmnls]) THEN
	    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    `[TS t'] = y1` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    SRW_TAC [][] THEN
	    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  FIRST_X_ASSUM (Q.SPECL_THEN [`dl2`,`y2`,`[]`,`s`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `symRepProp (MAP (addFront [TS t']) dl2)`
		  by METIS_TAC [EVERY_DEF, symRepPropAddFront] THEN
		  Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		  METIS_TAC [],

		  FIRST_X_ASSUM (Q.SPECL_THEN [`dl2`,`y2`,`t++[TS t']`,`s`]
				 MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `symRepProp (MAP (addFront [TS t']) dl2)`
		  by METIS_TAC [EVERY_DEF, symRepPropAddFront, APPEND,
				APPEND_ASSOC] THEN
		  Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		  METIS_TAC []
		  ]]]);


val symPropExistsGen = store_thm
("symPropExistsGen",
``∀dl x y p s.
lderives g ⊢ dl ◁ x → y ∧ MEM (p ++ x ++ s) (TL dl) ∧ isWord y
⇒ symRepProp dl``,

SRW_TAC [][] THEN
Cases_on `isWord p` THEN1
METIS_TAC [symPropExistsGen0] THEN
IMP_RES_TAC leftnt THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [][] THEN
`∃tl.MEM (l1 ++ tl++ x ++ s) (TL dl) ∧ isWord tl`
by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [][] THEN
    Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN
    `(h::(r1 ++ [l1 ++ [NTS n] ++ l2 ++ h ++ s] ++ r2)) =
    ([h]++r1) ++ [l1 ++ ([NTS n] ++ l2) ++ (h ++ s)] ++ r2`
   by METIS_TAC [APPEND_ASSOC, APPEND] THEN
    `¬isWord ([NTS n]++l2)` by SRW_TAC [][isTmnlSym_def] THEN
    `∃r1' r2' tl.(r2 = r1' ++ [l1 ++ tl ++ (h++s)] ++ r2') ∧ isWord tl`
    by METIS_TAC [rtc2listldFstNt'] THEN
    SRW_TAC [][] THEN
    METIS_TAC [APPEND, APPEND_ASSOC]) THEN
`isWord (l1++tl)`by SRW_TAC [][] THEN
METIS_TAC [symPropExistsGen0, APPEND_ASSOC, APPEND]);


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
  ¬symRepProp dl1 ∧ ¬symRepProp dl2 ∧ distElemLen dl dl1 ∧ distElemLen dl dl2 ∧
 (LENGTH (distinctldNts dl2) ≤ LENGTH (distinctldNts dl))`;


val l1 = prove
(``EVERY isTmnlSym x ⇒ [x] ≠ p ++ [tsl ++ [NTS B] ++ sfx'] ++ s``,

SRW_TAC [][lreseq] THEN
Q_TAC SUFF_TAC `tsl ++ [NTS B] ++ sfx' ≠ x` THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);

val ldSplitDeriv = store_thm
("ldSplitDeriv",
``∀x y v pfx sfx.
 (lderives g) ⊢ dl ◁ (x ++ y) → v  ∧ isCnf g ∧
 EVERY isTmnlSym v ∧
 (pfx++sfx = x++y) ∧ EVERY isTmnlSym pfx ∧ EVERY isNonTmnlSym sfx ∧
 ¬symRepProp dl
  ⇒
  ∃dl1 dl2 x' y'.
  splitDerivProp (g,dl,v) (dl1,x,x') (dl2,y,y')``,

completeInduct_on `LENGTH dl` THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def, symRepProp_def] THEN
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

`¬symRepProp ((s1++rhs++s2)::t')` by METIS_TAC [spropApp,TL,NOT_CONS_NIL] THEN
`(LENGTH rhs = 2) ∧ EVERY isNonTmnlSym rhs ∨
    (LENGTH rhs = 1) ∧ EVERY isTmnlSym rhs`
by METIS_TAC [isCnf_def]
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
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symRepProp_def] THEN
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
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`h`,`B`,`s2`,`v`,`w`,
						`(h ++ NTS n::NTS n'::s2)::
						(MAP (addFront h) t' ++
						 [h ++ v ++ [NTS B] ++ w ++ s2] ++
						 MAP (addFront h) s1)`] MP_TAC) THEN
		    SRW_TAC [][] THEN
		    SPOSE_NOT_THEN ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    `s1 ≠ []` by
		     (SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      `EVERY isTmnlSym (v ++ [NTS B] ++ w ++ s2)`
		      by METIS_TAC [last_elem, APPEND, APPEND_ASSOC,
				    EVERY_APPEND] THEN
		      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN1
		     METIS_TAC [NOT_EVERY] THEN
		     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		     FIRST_X_ASSUM (Q.SPECL_THEN
				    [`(h ++ NTS n::NTS n'::s2)::
				     (MAP (addFront h) t')`,`MAP (addFront h) s1`]
				      MP_TAC) THEN
		     SRW_TAC [][] THEN
		     SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN1
		     METIS_TAC [NOT_EVERY] THEN1
 		     (`¬EXISTS ($~ o isTmnlSym) []`
		      by METIS_TAC [NOT_EVERY, EVERY_DEF] THEN
		      `(h ++ NTS n::NTS n'::s2 =
			h ++ [] ++ [NTS n] ++ [NTS n'] ++ s2)`
		      by METIS_TAC [APPEND_NIL, APPEND, APPEND_ASSOC] THEN
		      METIS_TAC []) THEN
		     METIS_TAC [leftmostAddFront', existsThrice, NOT_EVERY]
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
		   Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		   Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		   Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		   Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		   FIRST_X_ASSUM (Q.SPECL_THEN
				  [`(h ++ [NTS lhs] ++ s2)::(MAP (addFront h) t'')`,
				   `h ++ tsl`,`B`,`sfx`,`v`,`w`,
				   `MAP (addFront h) s0 ++
				   [h ++ tsl ++ v ++ [NTS B] ++ w ++ sfx] ++
				   MAP (addFront h) s1`] MP_TAC) THEN
		   SRW_TAC [][]
		   THENL[
			 METIS_TAC [NOT_EVERY],

			 METIS_TAC [NOT_EVERY],


			 SPOSE_NOT_THEN ASSUME_TAC THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [][] THEN
			 Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
			 Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
			 Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
			 Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`MAP (addFront h) s0`,
						      `MAP (addFront h) s1`] MP_TAC) THEN
			 SRW_TAC [][] THEN
			 SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN1
			 METIS_TAC [leftmostAddFront', existsThrice, NOT_EVERY] THEN
			 Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
					[`t''`,`tsl`,`B`,`sfx`,`v`,`w`,
					 `s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`] MP_TAC) THEN
			 SRW_TAC [][] THEN
			 METIS_TAC [everyNotTwice, existsThrice, NOT_EVERY]],

			 FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
			 SRW_TAC [][] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
			 ]) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN
	    (FULL_SIMP_TAC (srw_ss()) [distElemLen_def, LENGTH_distinctldNts] THEN
	     `MAP (λl. addLast l (rhs ++ s2)) dl1 ++ MAP (addFront x'') (TL dl2)
                 = (pfx++rhs++s2)::t'` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q_TAC SUFF_TAC `set (ldNts ((NTS lhs::s2)::dl2)) ⊆
	     set (ldNts ((pfx ++ [NTS lhs] ++ s2)::(pfx ++ rhs ++ s2)::t'))` THEN1
	     METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
	     FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, EXTENSION,
				       SUBSET_DEF, distElemSubset_def,
				       distinctldNts_def, FILTER_APPEND] THEN
	     METIS_TAC [MEM, MEM_APPEND, rmd_r2]),

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
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symRepProp_def] THEN
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
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.ABBREV_TAC `z=(LAST ((pfx ++ [NTS n; NTS n'] ++ pfx')::
					   (t'' ++ [pfx ++ v ++ [NTS B] ++ w ++ pfx']
					    ++ s1)))` THEN
		    FIRST_X_ASSUM (Q.SPECL_THEN
				   [`[]`,`pfx`,`B`,`pfx'++h`,`v`,`w`,
				    `(pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
				    (MAP (λl. l ++ h) t'' ++
				     [pfx ++ v ++ [NTS B] ++ w ++ pfx' ++ h] ++
				     MAP (λl. l ++ h) s1 ++ MAP (addFront z) t)`]
				   MP_TAC) THEN
		    SRW_TAC [][] THEN1
		    METIS_TAC [NOT_EVERY] THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    FIRST_X_ASSUM (Q.SPECL_THEN
				   [`(pfx ++ [NTS n; NTS n'] ++ pfx' ++ h)::
				    MAP (λl. l ++ h) t''`,
				    `MAP (λl. l ++ h) s1 ++ MAP (addFront z) t`]
				   MP_TAC) THEN SRW_TAC [][] THEN1
		    METIS_TAC [NOT_EVERY] THEN1
		    METIS_TAC [NOT_EVERY] THEN
		    SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
		    FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
		    SRW_TAC [][] THEN
		    `∃p0 p1 nt.(l = pfx ++ p0 ++ [NTS nt] ++ p1 ++ pfx') ∧
           	      EVERY ($~ o $~ o isTmnlSym) p0` by METIS_TAC [] THEN
		    SRW_TAC [][] THEN
		    METIS_TAC [APPEND_ASSOC, APPEND_11, EVERY_APPEND,
			       everyNotTwice, NOT_EXISTS]
		    ]) THEN

	     FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     Q.ABBREV_TAC `s1' =
	    MAP (addFront (LAST (t'' ++ [tsl ++ [NTS B] ++ sfx'] ++ s0 ++
				 [tsl ++ v ++ [NTS B] ++ w ++ sfx'] ++s1))) t` THEN
	     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
	     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN
			    [`t''`,`tsl`,`B`,`sfx'`,`v`,`w`,
			     `s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx'] ++ s1`]
			    MP_TAC) THEN
	     SRW_TAC [][] THEN1
	     METIS_TAC [NOT_EVERY] THEN
	     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`s0`,`s1`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [NOT_EVERY]) THEN1

	    (FULL_SIMP_TAC (srw_ss()) [distElemLen_def, LENGTH_distinctldNts] THEN
	    `MAP (λl. addLast l sfx) dl1 ++ MAP (addFront x'') (TL dl2)
                 = (pfx++rhs++pfx'++sfx)::t'` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q_TAC SUFF_TAC `(set (ldNts ((pfx ++ [NTS lhs] ++ pfx')::dl1))) ⊆
               set (ldNts ((pfx ++ [NTS lhs] ++ pfx' ++ sfx)::
			   (pfx ++ rhs ++ pfx' ++ sfx)::t'))` THEN1
	     METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
	    FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, EXTENSION,
				      SUBSET_DEF, distElemSubset_def,
				      distinctldNts_def, FILTER_APPEND] THEN
	     METIS_TAC [MEM, MEM_APPEND, rmd_r2]) THEN1
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
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symRepProp_def] THEN
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
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    FIRST_X_ASSUM (Q.SPECL_THEN
				   [`[]`,`h++sfx`,`B`,`s2`,`v`,`w`,
				    `(h ++ sfx ++ [NTS n; NTS n'] ++ s2)::
				    (MAP (addFront h) t'' ++
				     [h ++ sfx ++ v ++ [NTS B] ++ w ++ s2] ++
				     MAP (addFront h) s1)`] MP_TAC) THEN
		    SRW_TAC [][] THEN1
		    METIS_TAC [NOT_EVERY] THEN1
		    METIS_TAC [NOT_EVERY] THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
		    FIRST_X_ASSUM (Q.SPECL_THEN
				   [`(h ++ sfx ++ [NTS n; NTS n'] ++ s2)::
				    MAP (addFront h) t''`,
				    `MAP (addFront h) s1`] MP_TAC) THEN
		    SRW_TAC [][] THEN1
		    METIS_TAC [NOT_EVERY] THEN1
		    METIS_TAC [APPEND_11, APPEND_ASSOC, NOT_EVERY] THEN
		    FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
		    SRW_TAC [][] THEN
		    FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		    SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
		    METIS_TAC [APPEND_11, APPEND_ASSOC, NOT_EVERY]]) THEN

	     Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	     Q.PAT_X_ASSUM `∀e.P e` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN
			    [`t''`,`tsl`,`B`,`sfx'`,`v`,`w`,
			     `s0 ++ [tsl ++ v ++ [NTS B] ++ w ++ sfx'] ++ s1`]
			    MP_TAC) THEN SRW_TAC [][] THEN
	     METIS_TAC [NOT_EVERY, everyNotTwice]) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN
	    (FULL_SIMP_TAC (srw_ss()) [distElemLen_def, LENGTH_distinctldNts] THEN
	    `MAP (λl. addLast l (sfx++rhs++s2)) dl1 ++ MAP (addFront x'') (TL dl2)
                 = (pfx'++sfx++rhs++s2)::t'` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q_TAC SUFF_TAC `set (ldNts ((sfx ++ [NTS lhs] ++ s2)::dl2)) ⊆
               set (ldNts ((pfx' ++ sfx ++ [NTS lhs] ++ s2)::
			   (pfx' ++ sfx ++ rhs ++ s2)::t'))` THEN1
	     METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
	    FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, EXTENSION,
				      SUBSET_DEF, distElemSubset_def,
				      distinctldNts_def, FILTER_APPEND] THEN
	     METIS_TAC [MEM, MEM_APPEND, rmd_r2])
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

	    (FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
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
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN
	    (FULL_SIMP_TAC (srw_ss()) [distElemLen_def, LENGTH_distinctldNts] THEN
	    `MAP (λl. addLast l (rhs++s2)) dl1 ++ MAP (addFront x'') (TL dl2)
                 = (pfx++rhs++s2)::t'` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q_TAC SUFF_TAC `set (ldNts ((NTS lhs::s2)::dl2)) ⊆
               set (ldNts ((pfx ++ [NTS lhs] ++ s2)::
			   (pfx++ rhs ++ s2)::t'))` THEN1
	     METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
	    FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, EXTENSION,
				      SUBSET_DEF, distElemSubset_def,
				      distinctldNts_def, FILTER_APPEND] THEN
	     METIS_TAC [MEM, MEM_APPEND, rmd_r2]),


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


	    (FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
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
	     Q.PAT_X_ASSUM `∀e.P` MP_TAC THEN
	     Q.PAT_X_ASSUM `∀e.P` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN
			    [`t'''`,`tsl`,`B`,`sfx`,`v`,`w`,
			     `s0 ++[tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`]
			    MP_TAC) THEN
	     SRW_TAC [][] THEN
	     `EXISTS ($~ o $~ o $~ o isTmnlSym) p0 =
	    EXISTS ($~ o isTmnlSym) p0` by METIS_TAC [existsThrice] THEN
	     METIS_TAC [everyNotTwice, NOT_EVERY]
	     ) THEN1

	    (FULL_SIMP_TAC (srw_ss()) [distElemLen_def, LENGTH_distinctldNts] THEN
	    `MAP (λl. addLast l sfx') dl1 ++ MAP (addFront x'') (TL dl2)
                 = (pfx++rhs++pfx'++sfx')::t'` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q_TAC SUFF_TAC `(set (ldNts ((pfx ++ [NTS lhs] ++ pfx')::dl1))) ⊆
               set (ldNts ((pfx ++ [NTS lhs] ++ pfx' ++ sfx')::
			   (pfx ++ rhs ++ pfx' ++ sfx')::t'))` THEN1
	     METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
	    FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, EXTENSION,
				      SUBSET_DEF, distElemSubset_def,
				      distinctldNts_def, FILTER_APPEND] THEN
	     METIS_TAC [MEM, MEM_APPEND, rmd_r2])  THEN1
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
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def, symRepProp_def] THEN
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
	     Q.PAT_X_ASSUM `∀e.P` MP_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN
			    [`t'''`,`tsl`,`B`,`sfx`,`v`,`w`,
			     `s0 ++[tsl ++ v ++ [NTS B] ++ w ++ sfx] ++ s1`]
			    MP_TAC) THEN
	     SRW_TAC [][] THEN
	     METIS_TAC [everyNotTwice, NOT_EVERY]) THEN1
	    METIS_TAC [distLenAddElem, APPEND, APPEND_ASSOC, distElemLen_def] THEN
	    (FULL_SIMP_TAC (srw_ss()) [distElemLen_def, LENGTH_distinctldNts] THEN
	    `MAP (λl. addLast l (sfx'++rhs++s2)) dl1 ++ MAP (addFront x'') (TL dl2)
                 = (pfx'++sfx'++rhs++s2)::t'` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q_TAC SUFF_TAC `set (ldNts ((sfx' ++ [NTS lhs] ++ s2)::dl2)) ⊆
               set (ldNts ((pfx' ++ sfx' ++ [NTS lhs] ++ s2)::
			   (pfx' ++ sfx' ++ rhs ++ s2)::t'))` THEN1
	     METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
	    FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, EXTENSION,
				      SUBSET_DEF, distElemSubset_def,
				      distinctldNts_def, FILTER_APPEND] THEN
	     METIS_TAC [MEM, MEM_APPEND, rmd_r2])
	    ]]);



val inpLen = store_thm
("inpLen",
``∀k A z.
    (lderives g) ⊢ (dl:(α,β) symbol list list) ◁ [NTS A] → z ∧
    (k = LENGTH (distinctldNts dl)) ∧
    EVERY isTmnlSym z ∧
    isCnf g ∧
    ¬symRepProp dl
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
    (LENGTH h' = 1) ∧ EVERY isTmnlSym h'` by METIS_TAC [isCnf_def,lderives_def,
							APPEND_NIL,lreseq]
THENL[

FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
SRW_TAC [][] THEN
`lderives g ⊢ [e1; e2]::t' ◁ [e1]++ [e2] → z` by METIS_TAC [APPEND] THEN
`∃pfx sfx.
      (pfx++sfx = [e1]++[e2]) ∧
      EVERY isTmnlSym pfx ∧ EVERY isNonTmnlSym sfx`
      by METIS_TAC [APPEND_NIL,EVERY_DEF,APPEND] THEN
`EVERY isNonTmnlSym ([e1]++[e2])` by METIS_TAC [APPEND,EVERY_DEF] THEN
`¬symRepProp ([e1; e2]::t')` by METIS_TAC [NOT_EVERY,spropApp,TL,NOT_CONS_NIL] THEN
`∀tsl e sfx.LENGTH (tsl ++ [e] ++ sfx) + 1 = LENGTH tsl + 1 + LENGTH sfx + 1`
      by SRW_TAC [][] THEN

Q.PAT_X_ASSUM `lderives g ⊢ h::[e1; e2]::t' ◁ [NTS A] → z` MP_TAC THEN

`∃dl1 dl2 x' y'.
splitDerivProp (g,[e1; e2]::t',z) (dl1,[e1],x') (dl2,[e2],y')`
      by  (Q.ABBREV_TAC `dl=[e1; e2]::t'` THEN
	   Q.ABBREV_TAC `el1 = [e1]` THEN
	   Q.ABBREV_TAC `el2 = [e2]` THEN
	   METIS_TAC [ldSplitDeriv]) THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e1` THEN Cases_on `e2` THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`LENGTH dl1 < (SUC (SUC (LENGTH t')))` by DECIDE_TAC THEN
`LENGTH dl2 < (SUC (SUC (LENGTH t')))` by DECIDE_TAC THEN
`lderives g ⊢ dl1 ◁ [NTS n] → x' ∧ ¬symRepProp dl1
⇒
LENGTH x' ≤
2 ** (LENGTH (distinctldNts dl1) − 1)` by METIS_TAC [] THEN
`lderives g ⊢ dl2 ◁ [NTS n'] → y' ∧ ¬symRepProp dl2  ⇒
	   LENGTH y' ≤
	   2 ** (LENGTH (distinctldNts dl2) − 1)` by METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH x' ≤ 2 ** (LENGTH (distinctldNts dl1) − 1)` by METIS_TAC [symRepProp_def,
								  NOT_EVERY] THEN
`LENGTH y' ≤ 2 ** (LENGTH (distinctldNts dl2) − 1)` by METIS_TAC [symRepProp_def,
								  NOT_EVERY] THEN
`h=[NTS A]` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [distElemLen_def] THEN
 `¬MEM (NTS A) (ldNts dl1)` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [distElemSubset_def] THEN
 `∃e. MEM e dl1 ∧ MEM (NTS A) e`  by METIS_TAC [memldNts] THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [MAP_APPEND, addLast_def] THEN
 METIS_TAC [symPropExists, APPEND, APPEND_ASSOC, EVERY_APPEND]) THEN

 `¬MEM (NTS A) (ldNts dl2)` by
 (SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [distElemSubset_def] THEN
 `∃e. MEM e dl2 ∧ MEM (NTS A) e`  by METIS_TAC [memldNts] THEN
  `∃r1 r2.e = r1 ++ [NTS A] ++ r2` by METIS_TAC [rgr_r9eq] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [MAP_APPEND, addLast_def, addFront_def] THEN
  `dl2 ≠ []` by (Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
  `dl2 = HD dl2::TL dl2` by METIS_TAC [CONS, NULL_EQ_NIL] THEN
  `(HD dl2 = r1++[NTS A]++r2 ) ∨ MEM (r1++[NTS A]++r2) (TL dl2)`
  by METIS_TAC [MEM] THEN
  SRW_TAC [][]
  THENL[
	(* HD dl2 *)
	`r1++ [NTS A]++r2 = [NTS n']` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [][] THEN
	`dl1 ≠ []` by (Cases_on `dl1` THEN SRW_TAC [][] THEN
		       FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	`∃e.MEM e dl1` by METIS_TAC [listNotEmpty] THEN
	`∃r1 r2.dl1 = r1 ++ [e] ++ r2`by METIS_TAC [rgr_r9eq] THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [MAP_APPEND] THEN
	`[NTS A]::(MAP (λl. l ++ [NTS A]) r1 ++
        [e ++ [NTS A]] ++ MAP (λl. l ++ [NTS A]) r2 ++MAP (addFront x') (TL dl2)) =
	[[NTS A]]++MAP (λl. l ++ [NTS A]) r1 ++
        [e ++ [NTS A] ++ []] ++ (MAP (λl. l ++ [NTS A]) r2 ++MAP (addFront x') (TL dl2))`
	by METIS_TAC [APPEND_NIL, APPEND, APPEND_ASSOC] THEN
	METIS_TAC [symPropExists,EVERY_APPEND],

	(* A in TL dl2 *)
	`∃r11 r22.TL dl2 = r11 ++ [r1++[NTS A]++r2] ++ r22`
	by METIS_TAC [rgr_r9eq] THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
	`[NTS A]::(MAP (λl. l ++ [NTS n']) dl1 ++
         MAP (addFront x') r11 ++[x' ++ r1 ++ [NTS A] ++ r2] ++MAP (addFront x') r22)
	=[[NTS A]]++(MAP (λl. l ++ [NTS n']) dl1 ++
         MAP (addFront x') r11) ++[(x' ++ r1) ++ [NTS A] ++ r2] ++
	MAP (addFront x') r22` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	METIS_TAC [symPropExists,EVERY_APPEND]]) THEN

`LENGTH (distinctldNts dl1) ≤
           LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) - 1`
by
(FULL_SIMP_TAC (srw_ss()) [LENGTH_distinctldNts] THEN
 Q_TAC SUFF_TAC `CARD (set (ldNts dl1)) <
 CARD (set (ldNts ([NTS A]::[NTS n; NTS n']::t')))` THEN
SRW_TAC [][] THEN1
 DECIDE_TAC THEN
Q_TAC SUFF_TAC `set (ldNts dl1) ⊂ (set (ldNts ([NTS A]::[NTS n; NTS n']::t')))` THEN1
 METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, PSUBSET_DEF, EXTENSION,
			   SUBSET_DEF, isNonTmnlSym_def, distElemSubset_def,
			   distinctldNts_def] THEN
 METIS_TAC [rmd_r2, MEM, MEM_APPEND]) THEN

`LENGTH (distinctldNts dl2) ≤
           LENGTH (distinctldNts ([NTS A]::[NTS n; NTS n']::t')) -1`
by (FULL_SIMP_TAC (srw_ss()) [LENGTH_distinctldNts] THEN
 Q_TAC SUFF_TAC `CARD (set (ldNts dl2)) <
 CARD (set (ldNts ([NTS A]::[NTS n; NTS n']::t')))` THEN SRW_TAC [][] THEN1
 DECIDE_TAC THEN
Q_TAC SUFF_TAC `set (ldNts dl2) ⊂ (set (ldNts ([NTS A]::[NTS n; NTS n']::t')))` THEN1
 METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ldNts_def, FILTER_APPEND, PSUBSET_DEF, EXTENSION,
			   SUBSET_DEF, isNonTmnlSym_def, distElemSubset_def,
			   distinctldNts_def] THEN
 METIS_TAC [rmd_r2, MEM, MEM_APPEND]) THEN
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
 FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN

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
FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [],

FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def,lreseq] THEN
SRW_TAC [][distinctldNts_def,ldNts_def,rmDupes,delete_def]]);



val lastExpProp = Define
`lastExpProp (g,dl,z) =
(∃p s tsl B sfx N1 N2.
 ntProp dl p s tsl B sfx N1 N2 ∧
  ∃dl1 dl2 dl3 v w.
  lderives g ⊢ dl1 ◁ [NTS N1;NTS N2] → (v++[NTS B]++w) ∧
  ∃rst.lderives g ⊢ dl2 ◁  (v++[NTS B]++w) → (v++rst) ∧
  ∃rst'.lderives g ⊢ dl3 ◁ sfx → rst' ∧
  (z = tsl++v++rst++rst') ∧
  distElemSubset dl dl1 ∧
  distElemSubset dl dl2 ∧
  distElemSubset dl dl3 ∧
  (∀e.MEM e dl1 ⇒ MEM (tsl ++ e ++ sfx) dl) ∧
  (∀e.MEM e dl2 ⇒ MEM (tsl ++ e ++sfx) dl) ∧
  ¬symRepProp dl1 ∧ ¬symRepProp dl2 ∧ ¬(symRepProp (dl1++(TL dl2))))`;



val addFrontrtc2list = store_thm
("addFrontrtc2list",
``∀l.rtc2list (lderives g) l ∧ EVERY isTmnlSym rhs
    ⇒
    rtc2list (lderives g) (MAP (addFront rhs) l)``,

Induct_on `l` THEN SRW_TAC [][addFront_def] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
METIS_TAC [lderives_same_append_left]);


val listsecldSfxNil = store_thm
("listsecldSfxNil",
``∀dl x.
     lderives g ⊢ dl ◁ (p++x) → (p++y) ∧ EVERY isTmnlSym p
   ⇒
     lderives g ⊢ MAP (listsec p []) dl ◁ listsec p [] (p++x) → listsec p [] (p++y)``,
let 
 val tac = 
  IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
  IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] 
    >- METIS_TAC [listsecDropNilSfx,
                   APPEND_NIL,APPEND_ASSOC,APPEND,EVERY_DEF,EVERY_APPEND]
    >- METIS_TAC [APPEND_ASSOC,listsecDropNilSfx,APPEND_NIL,
                  APPEND,EVERY_DEF,EVERY_APPEND]
    >- (FULL_SIMP_TAC (srw_ss()) [] THEN
        SRW_TAC [][] THEN
        `s1''=[]`  
         by (Cases_on `s1''` THEN SRW_TAC [][] THEN
             Cases_on `h` THEN 
             FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
        SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        SRW_TAC [][] THEN
        METIS_TAC [listsecDropNilSfx,
          APPEND_NIL,APPEND_ASSOC,APPEND,EVERY_DEF,EVERY_APPEND])
in 
  Induct_on `dl` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  Cases_on `dl` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listsecDropNilSfx] THEN
  FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
  SRW_TAC [][] 
 >- tac
 >- tac
 >- (Q_TAC SUFF_TAC `LAST (MAP (listsec p []) ((s1 ++ rhs ++ s2)::t)) = y`
       >- metis_tac [MAP] >>
     Q_TAC SUFF_TAC `listsec p [] (LAST ((s1 ++ rhs ++ s2)::t)) = y`
       >- metis_tac [LAST_MAP,list_distinct] >>
     metis_tac [listsecDropNilSfx])
end
);

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


val dldntsMemListEq' = store_thm
("dldntsMemListEq'",
``∀l.(MEM e (distinctldNts l) ⇔ MEM e (FILTER isNonTmnlSym (FLAT l)))``,
Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [distinctldNts_def,ldNts_def,rmDupes] THEN
SRW_TAC [][FILTER_APPEND, EQ_IMP_THM] THEN1
(`MEM e (FILTER isNonTmnlSym (h ++ FLAT l))` by METIS_TAC [rmd_r2, FILTER_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_FILTER]) THEN
METIS_TAC [rmd_r2, MEM_APPEND]);


val distesubtrans = store_thm
("distesubtrans",
``distElemSubset dl dl1 ∧ distElemSubset dl1 dl0 ⇒
 distElemSubset dl dl0``,

SRW_TAC [][distElemSubset_def]);


val listAddFrontLast = store_thm
("listAddFrontLast",
``∀l.(∀e.MEM e l ⇒
MEM (p ++ e ++ s) (MAP (λl. addLast l s) (MAP (addFront p) l)))``,

Induct_on `l` THEN SRW_TAC [][addLast_def, addFront_def] THEN
METIS_TAC [addLast_def]);


val lastExp = store_thm
("lastExp",
``∀dl z0 pz0 sz0.
 (lderives g) ⊢ dl ◁ z0 → z ∧ isCnf g ∧ EVERY isTmnlSym z ∧
 (z0=pz0++sz0) ∧ EVERY isTmnlSym pz0 ∧ EVERY isNonTmnlSym sz0 ∧
 symRepProp dl
 ⇒
 lastExpProp (g,dl,z)``,


Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

 (FULL_SIMP_TAC (srw_ss()) [lderives_def, lastExpProp, listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
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
Cases_on `symRepProp ((pz0' ++ sz0')::t)` THEN1
(`lastExpProp (g,(pz0' ++ sz0')::t,z)` by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [lastExpProp] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ntProp_def] THEN SRW_TAC [][] THEN1

(MAP_EVERY Q.EXISTS_TAC [`h::p`,`s`,`tsl`,`B`,`sfx`, `B`,`N2`] THEN
 SRW_TAC [][] THEN
 MAP_EVERY Q.EXISTS_TAC [`dl1`,`dl2`,`dl3`,`v`,`w`] THEN SRW_TAC [][] THEN
 Q.EXISTS_TAC `rst` THEN SRW_TAC [][] THEN
 METIS_TAC [distesubaddlist, APPEND_NIL, APPEND]) THEN

 MAP_EVERY Q.EXISTS_TAC [`h::p`,
			`r1 ++[tsl ++ v' ++ [NTS B] ++ w' ++ sfx] ++ r2`,
			 `tsl`,`B`,`sfx`, `N1`,`N2`] THEN
 SRW_TAC [][] THEN1
 METIS_TAC [] THEN
 MAP_EVERY Q.EXISTS_TAC [`dl1`,`dl2`,`dl3`,`v`,`w`] THEN SRW_TAC [][] THEN
 Q.EXISTS_TAC `rst` THEN SRW_TAC [][] THEN
 METIS_TAC [distesubaddlist, APPEND_NIL, APPEND, APPEND_ASSOC]) THEN

(* ¬symRepProp ((pz0' ++ sz0')::t) *)
FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
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
by METIS_TAC [isCnf_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [lastExpProp, ntProp_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`, `s1`,`s1'`,`B`,`s2`,`B`,`n`] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN
`EVERY isNonTmnlSym ([NTS B] ++ [NTS n] ++ s2)`
by FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, EVERY_APPEND] THEN
`¬symRepProp ((s1' ++ [NTS B] ++ [NTS n] ++ s2)::s1)`
by (FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
    SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []) THEN
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
(`x' = s1'` by
 (Cases_on `dl3` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  `t=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`∀e.MEM e ((s1' ++ [NTS B] ++ [NTS n] ++ s2)::s1) =
          MEM e (MAP (λl. addLast l s2)
		 (MAP (λl. addLast l [NTS B; NTS n]) dl3) ++
		 MAP (λl. addLast l s2) (MAP (addFront s1') (TL dl4)) ++
		 MAP (addFront (s1' ++ y')) (TL dl2))`
by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(dl4 ≠ []) ∧ (HD dl4 = [NTS B; NTS n])` by
 (Cases_on `dl4` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
`dl4 = [NTS B;NTS n]::TL dl4` by METIS_TAC [CONS, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN
`MEM e ([NTS B; NTS n]::TL dl4)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [APPEND, APPEND_11, APPEND_ASSOC] THEN
`MEM e dl4` by METIS_TAC [MEM, NULL_EQ_NIL, NOT_CONS_NIL] THEN
METIS_TAC [listAddFrontLast, APPEND, APPEND_ASSOC, APPEND_11]) THEN1

(* 6 *)
(FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
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
by METIS_TAC [isCnf_def] THEN1
(* nonTmnl rule *)

(FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
Cases_on `e1` THEN Cases_on `e2` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp, ntProp_def] THEN
`(s1' = pz0') ∧ ([NTS n;NTS n']++s2 = sz0')` by METIS_TAC [symListDiv, APPEND,
							   APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`[]:(α,β) symbol list list`,
			`(t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1)`,
			`pz0'`,`B`,`s2`,`n`,`n'`] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN
`EVERY isNonTmnlSym ([NTS n] ++ [NTS n'] ++ s2)`
by FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, EVERY_APPEND] THEN
`(pz0' ++ NTS n::NTS n'::s2 = (pz0' ++ [NTS n] ++ [NTS n']) ++ s2)`
by METIS_TAC [APPEND, APPEND_ASSOC] THEN
`¬symRepProp ((pz0' ++ NTS n::NTS n'::s2)::
(t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1))` by
(FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []) THEN
`∃dl1 dl2 x y. splitDerivProp (g,(pz0' ++ NTS n::NTS n'::s2)::
			       (t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1),z)
(dl1,pz0'++[NTS n]++[NTS n'],x) (dl2,s2,y)`
by METIS_TAC [ldSplitDeriv] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
`dl1 ≠ []` by (Cases_on `dl1` THEN
	       FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
Cases_on `dl1` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN SRW_TAC [][] THEN
(* ldSplitDeriv *)
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
`MAP (λl. l ++ s2) t ++ MAP (addFront x) (TL dl2) =
t' ++ ([pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1)`
by METIS_TAC [APPEND, APPEND_ASSOC] THEN
Q.ABBREV_TAC `l1 = MAP (λl. l ++ s2) t` THEN
Q.ABBREV_TAC `rst = MAP (addFront x) (TL dl2)` THEN
Q.ABBREV_TAC `l1' = t'` THEN
Q.ABBREV_TAC `rst' = [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1` THEN
`(l1 = l1') ∧ (rst = rst') ∨
(∃s1' s2'.(l1 = l1' ++ s1') ∧ (rst = s2') ∧ (rst' = s1' ++ s2')) ∨
∃s1' s2'. (l1' = l1 ++ s1') ∧ (rst' = s2') ∧ (rst = s1' ++ s2')`
by METIS_TAC [twoListAppEq] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
(`dl2 ≠ []`by (Cases_on `dl2` THEN
	       FULL_SIMP_TAC (srw_ss())  [listderiv_def]) THEN
 `dl2 = HD dl2::TL dl2` by METIS_TAC [NULL_EQ_NIL, CONS] THEN
 SRW_TAC [][] THEN
 UNABBREV_ALL_TAC THEN
 `MAP (addFront x) (TL dl2) = [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1`
 by METIS_TAC [APPEND_11, APPEND_ASSOC, APPEND] THEN
 Cases_on `TL dl2` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
 Cases_on `EVERY isTmnlSym h`  THEN1
 (`EVERY isTmnlSym (pz0' ++ v ++ [NTS B] ++ w ++ s2)`
  by METIS_TAC [EVERY_APPEND] THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
 IMP_RES_TAC leftnt THEN
 SRW_TAC [][] THEN
 `EVERY isNonTmnlSym [NTS B]` by SRW_TAC [][isNonTmnlSym_def] THEN
 `(x ++ l1) ++ [NTS n''] ++ l2 =
 (pz0' ++ v) ++ [NTS B] ++ (w ++ s2)` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
 `isWord (x++l1) ∧isWord (pz0'++v)` by METIS_TAC [EVERY_APPEND] THEN
 `[NTS B] ≠ []` by SRW_TAC [][] THEN
 `(x++l1 = pz0'++v) ∧ ([NTS n'']++l2 = [NTS B]++(w++s2))`
 by METIS_TAC [symlistdiv3] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
 `HD dl2 = s2` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 METIS_TAC [symPropExistsGen, APPEND, APPEND_ASSOC, APPEND_NIL, MEM])
THENL[

      Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN1
      (* s1' = [] *)
      (UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
      `MAP (addFront x) (TL dl2) = [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ s1`
      by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      `MEM (pz0' ++ v ++ [NTS B] ++ w ++ s2) (MAP (addFront x) (TL dl2))`
      by METIS_TAC [rgr_r9eq, MEM, MEM_APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [MEM_MAP, addFront_def] THEN
       Cases_on `EVERY isTmnlSym y'` THEN1
       (`EVERY isTmnlSym (pz0' ++ v ++ [NTS B] ++ w ++ s2)`
       by METIS_TAC [EVERY_APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       IMP_RES_TAC leftnt THEN SRW_TAC [][] THEN
       `(pz0' ++ v) ++ [NTS B] ++ (w ++ s2) =
         (x ++ l1) ++ [NTS n''] ++ l2` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	 `EVERY isNonTmnlSym [NTS B]` by SRW_TAC [][isNonTmnlSym_def] THEN
	 `isWord (x++l1) ∧isWord (pz0'++v)` by METIS_TAC [EVERY_APPEND] THEN
       `(pz0'++v = x ++ l1) ∧ ([NTS n'']++l2 = [NTS B] ++ (w ++ s2))`
       by METIS_TAC [NOT_CONS_NIL, symlistdiv3] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
       METIS_TAC [EVERY_APPEND, NOT_EVERY] THEN
       (`dl2 ≠ []`by (Cases_on `dl2` THEN
		     FULL_SIMP_TAC (srw_ss())  [listderiv_def]) THEN
       `dl2 = HD dl2::TL dl2` by METIS_TAC [NULL_EQ_NIL, CONS] THEN
       SRW_TAC [][] THEN
       `HD dl2 = s2` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       METIS_TAC [symPropExistsGen, APPEND, APPEND_ASSOC, APPEND_NIL, MEM])) THEN

      (* s1' ≠ [] *)
      UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
      `MAP (λl. l ++ s2) t = t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ t''`
      by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      `t = MAP (listsec ([]:(α,β) symbol list) s2)
          (t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ t'')`
      by METIS_TAC [addLastImpListsec] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `lderives g ⊢ (pz0' ++ [NTS n] ++ [NTS n'])::
      MAP (listsec ([]:(α,β) symbol list) s2) t' ++ [ listsec ([]:(α,β) symbol list) s2 (pz0' ++ v ++ [NTS B] ++ w ++ s2)]
       ◁ pz0' ++ [NTS n] ++ [NTS n'] →
       listsec ([]:(α,β) symbol list) s2 (pz0' ++ v ++ [NTS B] ++ w ++ s2)`
       by METIS_TAC [ldAppend, APPEND, APPEND_ASSOC, APPEND_NIL] THEN

       `lderives g ⊢[listsec ([]:(α,β) symbol list) s2 (pz0' ++ v ++ [NTS B] ++ w ++ s2)] ++
       MAP (listsec ([]:(α,β) symbol list) s2) t'' ◁
       listsec ([]:(α,β) symbol list) s2 (pz0' ++ v ++ [NTS B] ++ w ++ s2) → x`
       by METIS_TAC [ldAppend, APPEND, APPEND_ASSOC, APPEND_NIL] THEN
       `listsec ([]:(α,β) symbol list) s2 (pz0' ++ v ++ [NTS B] ++ w ++ s2) =
       pz0'++v ++ [NTS B] ++ w`
       by (SRW_TAC [][listsec_def, dropLast_def, REVERSE_APPEND] THEN
	   `(DROP (LENGTH s2)
	     (REVERSE s2 ++ REVERSE w ++ NTS B::(REVERSE v ++ REVERSE pz0')))
	   = REVERSE w ++ NTS B::(REVERSE v ++ REVERSE pz0')` by
	   METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND, APPEND_ASSOC,
		      LENGTH_REVERSE] THEN
	   FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND]) THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `isWord (pz0' ++ v)` by METIS_TAC [EVERY_APPEND] THEN
      `EVERY isNonTmnlSym ([NTS B] ++ w)` by
      (`MEM (pz0' ++ v ++ [NTS B] ++ w ++ s2)
       ((pz0' ++ [NTS B] ++ s2)::(pz0' ++ [NTS n] ++ [NTS n'] ++ s2)::
	(t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++
	 t'' ++ MAP (addFront x) (TL dl2)))` by METIS_TAC [MEM, MEM_APPEND] THEN
       `∃p s. (pz0' ++ v ++ [NTS B] ++ w ++ s2 = p ++ s) ∧ EVERY isTmnlSym p ∧
       EVERY isNonTmnlSym s` by METIS_TAC [ldMemlderivesPfxSfx] THEN
       `isWord (pz0'++v)` by SRW_TAC [][] THEN
       `(pz0' ++ v) ++ [NTS B] ++ (w ++ s2) = p ++ s`
       by METIS_TAC [APPEND_ASSOC] THEN
       `(pz0' ++ v = p) ∧ ([NTS B]++(w++s2) = s)` by METIS_TAC [symListDiv] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
       METIS_TAC [EVERY_DEF, EVERY_APPEND]) THEN
      `pz0' ++ v ++ [NTS B] ++ w = pz0' ++ (v ++ [NTS B] ++ w)`
      by METIS_TAC [APPEND_ASSOC] THEN
      `pz0' ++ v ++ [NTS B] ++ w = (pz0' ++ v) ++ ([NTS B] ++ w)`
      by METIS_TAC [APPEND_ASSOC] THEN
      `¬symRepProp ((pz0' ++ v ++ [NTS B] ++ w)::
		    MAP (listsec ([]:(α,β) symbol list) s2) t'')`
      by METIS_TAC [spropAppSnd, APPEND, APPEND_ASSOC,NOT_CONS_NIL] THEN
      `∃dl1' dl2' x' y'.
      splitDerivProp
      (g,(pz0' ++ v ++ [NTS B] ++ w)::MAP (listsec ([]:(α,β) symbol list) s2) t'',x)
      (dl1',pz0',x') (dl2',v ++ [NTS B] ++ w,y')`
      by METIS_TAC [ldSplitDeriv] THEN
      FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
      SRW_TAC [][] THEN
      `dl1' = [pz0']` by
      (Cases_on `dl1'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       SRW_TAC [][] THEN
       `t=[]` by METIS_TAC [rtc2listRtcldTmnls]) THEN
      SRW_TAC [][] THEN
      `x'=pz0'` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`MAP (listsec pz0'  ([]:(α,β) symbol list))
			      ((pz0' ++ [NTS n] ++ [NTS n'])::
			       (MAP (listsec  ([]:(α,β) symbol list) s2) t' ++
				[pz0' ++ v ++ [NTS B] ++ w]))`, `dl2'`,`dl2`] THEN
      MAP_EVERY Q.EXISTS_TAC [`v`,`w`] THEN SRW_TAC [][] THEN1
      (FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
      `lderives g ⊢
      MAP (listsec pz0' ([]:(α,β) symbol list)) ((pz0' ++ [NTS n] ++ [NTS n'])::
			     (MAP (listsec ([]:(α,β) symbol list) s2) t' ++
			      [pz0' ++ v ++ [NTS B] ++ w])) ◁
      listsec pz0' ([]:(α,β) symbol list) (pz0' ++ [NTS n] ++ [NTS n']) →
      listsec pz0' ([]:(α,β) symbol list) (pz0' ++ v ++ [NTS B] ++ w)`
      by METIS_TAC [listsecldSfxNil, APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `(listsec pz0' ([]:(α,β) symbol list)) (pz0' ++ [NTS n] ++ [NTS n']) = [NTS n] ++ [NTS n']`
      by METIS_TAC [listsecDropNilSfx, APPEND_ASSOC] THEN
      `listsec pz0' ([]:(α,β) symbol list) (pz0' ++ v ++ [NTS B] ++ w) = v ++ [NTS B] ++ w`
      by METIS_TAC [listsecDropNilSfx, APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) []) THEN
      `MEM y' dl2'` by METIS_TAC [memld] THEN
      `∃rst'.y' = v ++ rst'`by METIS_TAC [lderivesPfxSame, APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `rst'` THEN
      SRW_TAC [][] THEN1
      (* 9 subgoals *)
      (* 1 *)
      (`∀e.MEM e ((pz0' ++ [NTS n] ++ [NTS n'] ++ s2)::
		 t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2]) ⇒
      ∃rst.(e=pz0'++rst++s2)` by METIS_TAC [APPEND, APPEND_ASSOC,MEM,MEM_APPEND] THEN
      `((pz0' ++ [NTS B] ++ s2)::
           (pz0' ++ [NTS n] ++ [NTS n'] ++ s2)::
           (t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ t'' ++
            MAP (addFront (pz0' ++ v ++ rst')) (TL dl2))) =
      [pz0' ++ [NTS B] ++ s2] ++
      ((pz0' ++ [NTS n] ++ [NTS n'] ++ s2):: t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2])
      ++ (t'' ++ MAP (addFront (pz0' ++ v ++ rst')) (TL dl2))`
      by METIS_TAC [APPEND_ASSOC, APPEND] THEN
      `distElemSubset
      ((pz0' ++ [NTS B] ++ s2)::
       (pz0' ++ [NTS n] ++ [NTS n'] ++ s2)::
       (t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2] ++ t'' ++
	MAP (addFront (pz0' ++ v ++ rst')) (TL dl2)))
      (MAP (listsec pz0' s2) ((pz0' ++ [NTS n] ++ [NTS n'] ++ s2)::
			      t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2]))`
      by METIS_TAC [dldntsListsecPfx] THEN
      FULL_SIMP_TAC (srw_ss()) [addFront_def, addLast_def] THEN
      METIS_TAC [listsecPfxSfx, APPEND, APPEND_ASSOC,
		 listsecDropNilSfx, listsecSame]) THEN1

      (* 2 *)
            (FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
       METIS_TAC [distesubaddlist, APPEND, APPEND_ASSOC, APPEND_NIL,
		  distElemSS_trans]) THEN1

      (* 3 *)
      (FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
       METIS_TAC [distesubaddlist, APPEND, APPEND_ASSOC, APPEND_NIL,
		  distElemSS_trans]) THEN1

      (* 4 *)
      METIS_TAC [listsecDropNilSfx, APPEND_ASSOC] THEN1

      (* 5 *)
      (FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
       SRW_TAC [][] THEN
       `∃p0 p1 nt.(y'' = pz0' ++ p0 ++ [NTS nt] ++ p1 ++ s2) ∧
      isWord p0` by METIS_TAC [] THEN
       FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
      SRW_TAC [][] THEN
       `listsec pz0' ([]:(α,β) symbol list)
       (listsec ([]:(α,β) symbol list) s2 (pz0' ++ p0 ++ [NTS nt] ++ p1 ++ s2)) =
       p0 ++ [NTS nt] ++ p1`
       by METIS_TAC [listsecPfxSfx, APPEND, APPEND_ASSOC,APPEND_NIL] THEN
       SRW_TAC [][]) THEN1

      (* 6 *)
      METIS_TAC [listsecDropNilSfx, APPEND_ASSOC] THEN1

      (* 7 *)
      (FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
      `MAP (λl. l ++ s2) (MAP (listsec ([]:(α,β) symbol list) s2) t') = t'`
      by METIS_TAC [APPEND, APPEND_ASSOC, addLastListsec] THEN
      SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
      `dl2' ≠ []` by (Cases_on `dl2'` THEN
		      FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
      `dl2' = HD dl2'::TL dl2'` by METIS_TAC [CONS, NULL_EQ_NIL] THEN
      `HD dl2'=v ++ [NTS B] ++ w ` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl2'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN1
       (`rst' = [NTS B] ++w` by  METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
       SRW_TAC [][] THEN
       METIS_TAC [listAddFrontLast, addLast_def]) THEN
      METIS_TAC [listAddFrontLast, addLast_def]) THEN1

      (* 8 *)
      (`¬symRepProp
       ((pz0' ++ [NTS n] ++ [NTS n'] ++ s2)::
	(t' ++ [pz0' ++ v ++ [NTS B] ++ w ++ s2]))`
       by METIS_TAC [spropAppFst, APPEND, APPEND_ASSOC, NOT_CONS_NIL] THEN
       `isWord (pz0' ++ (v ++ rst'))` by SRW_TAC [][] THEN
       `pz0' ++ [NTS n] ++ [NTS n'] = pz0' ++ ([NTS n] ++ [NTS n'])`
       by METIS_TAC [APPEND_ASSOC] THEN
       `¬symRepProp
       (MAP (listsec pz0' ([]:(α,β) symbol list)) ((pz0' ++ [NTS n] ++ [NTS n'])::
       (MAP (listsec  ([]:(α,β) symbol list) s2) t' ++
	[pz0' ++ v ++ [NTS B] ++ w] ++
	MAP (listsec  ([]:(α,β) symbol list) s2) t'')))`
       by METIS_TAC [notspropLsTmnls] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [spropAppFst, APPEND, APPEND_ASSOC, NOT_CONS_NIL]) THEN
      (* 9 *)
      FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
      `lderives g ⊢
      ((pz0' ++ [NTS n] ++ [NTS n'])::(MAP (listsec ([]:(α,β) symbol list) s2) t' ++
				       [pz0' ++ v ++ [NTS B] ++ w])) ++
       MAP (addFront pz0') (TL dl2') ◁
      pz0' ++ [NTS n] ++ [NTS n'] → (pz0' ++ v ++ rst')`
      by METIS_TAC [listderivTrans, TL] THEN
      `pz0' ++ [NTS n] ++ [NTS n'] = pz0' ++ ([NTS n] ++ [NTS n'])`
      by METIS_TAC [APPEND_ASSOC] THEN
      `pz0'++v++rst' = pz0' ++ (v++rst')` by METIS_TAC [APPEND_ASSOC] THEN
      `isWord (pz0' ++ (v ++ rst'))` by SRW_TAC [][] THEN
      `¬symRepProp (MAP (listsec pz0' ([]:(α,β) symbol list))
		    ((pz0' ++ [NTS n] ++ [NTS n'])::
                   (MAP (listsec ([]:(α,β) symbol list) s2) t' ++
                    [pz0' ++ v ++ [NTS B] ++ w] ++
                    MAP (addFront pz0') (TL dl2'))))`
      by METIS_TAC [notspropLsTmnls] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [spropAppFst, APPEND, APPEND_ASSOC, NOT_CONS_NIL,
		 listsecAddFront],

      `dl2 ≠ []`by (Cases_on `dl2` THEN
		    FULL_SIMP_TAC (srw_ss())  [listderiv_def]) THEN
      `dl2 = HD dl2::TL dl2` by METIS_TAC [NULL_EQ_NIL, CONS] THEN
      SRW_TAC [][] THEN
       `HD dl2 = s2` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       `MAP (addFront x) (TL dl2) = s1' ++ (pz0' ++ v ++ [NTS B] ++ w ++ s2)::s1`
       by METIS_TAC [] THEN
       `MEM (pz0' ++ v ++ [NTS B] ++ w ++ s2) (MAP (addFront x) (TL dl2))`
       by METIS_TAC [rgr_r9eq, MEM, MEM_APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [MEM_MAP, addFront_def] THEN
      Cases_on `EVERY isTmnlSym y'` THEN1
      (`EVERY isTmnlSym (pz0' ++ v ++ [NTS B] ++ w ++ s2)`
       by METIS_TAC [EVERY_APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       IMP_RES_TAC leftnt THEN SRW_TAC [][] THEN
       `(pz0' ++ v) ++ [NTS B] ++ (w ++ HD dl2) =
         (x ++ l1') ++ [NTS n''] ++ l2` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	 `EVERY isNonTmnlSym [NTS B]` by SRW_TAC [][isNonTmnlSym_def] THEN
	 `isWord (x++l1') ∧isWord (pz0'++v)` by METIS_TAC [EVERY_APPEND] THEN
       `(pz0'++v = x ++ l1') ∧ ([NTS n'']++l2 = [NTS B] ++ (w ++ HD dl2))`
       by METIS_TAC [NOT_CONS_NIL, symlistdiv3] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
       METIS_TAC [EVERY_APPEND, NOT_EVERY] THEN
       METIS_TAC [symPropExistsGen, APPEND, APPEND_ASSOC, APPEND_NIL, MEM]
       ]) THEN

FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
Cases_on `e` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`∃p0 p1 nt.s1'++[TS t]++s2 = s1' ++ p0 ++ [NTS nt] ++ p1 ++ s2`
by METIS_TAC [] THEN
`[TS t] = p0++[NTS nt]++p1` by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
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
 symRepProp dl``,

 SRW_TAC [][] THEN
Q.ABBREV_TAC `k = LENGTH (distinctldNts dl)` THEN
`¬(LENGTH z ≤ 2 ** (k − 1))` by DECIDE_TAC THEN
METIS_TAC [inpLen]);



val rtcDerivesReplEnd = store_thm
("rtcDerivesReplEnd",
 ``∀i.(lderives g)^* [NTS B] (p ++ [NTS B] ++ s) ∧
 EVERY isTmnlSym p ∧
 (lderives g)^*  [NTS B] z ∧ EVERY isTmnlSym z ∧
 (lderives g)^* s z' ∧ EVERY isTmnlSym z'
  ⇒
  (lderives g)^* [NTS B] (FLAT (lpow p i) ++ z ++ FLAT (lpow z' i))``,

Induct_on `i` THEN SRW_TAC [][] THEN1
(SRW_TAC [][lpow_def,REPLICATE] THEN
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



val numdlds = store_thm
("numdlds",
``lderives g ⊢ dl ◁ [NTS (startSym g)] → z ⇒ LENGTH (distinctldNts dl) ≥ 1``,

SRW_TAC [][llanguage_def] THEN
FULL_SIMP_TAC (srw_ss()) [distinctldNts_def, ldNts_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][isNonTmnlSym_def, rmDupes] THEN
DECIDE_TAC);



val dldntsGe1 = store_thm
("dldntsGe1",
``∀dl x.lderives g ⊢ dl ◁ x → y ∧ LENGTH dl > 1 ⇒
	     LENGTH (distinctldNts dl) ≥ 1``,

Induct_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
SRW_TAC [][distinctldNts_def, ldNts_def, FILTER_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]
THENL[

 `MEM (NTS lhs) (rmDupes (FILTER isNonTmnlSym s1 ++ [NTS lhs] ++
			 FILTER isNonTmnlSym s2 ++ FILTER isNonTmnlSym s1 ++
			 FILTER isNonTmnlSym rhs ++ FILTER isNonTmnlSym s2))`
 by METIS_TAC [rmd_r2, rgr_r9eq, MEM, MEM_APPEND] THEN
METIS_TAC [MEM, NOT_CONS_NIL, LENGTH_NIL, DECIDE ``LENGTH l ≠ 0 ⇒ LENGTH l ≥ 1``],

 `MEM (NTS lhs) (rmDupes
         (FILTER isNonTmnlSym s1 ++ [NTS lhs] ++
          FILTER isNonTmnlSym s2 ++ FILTER isNonTmnlSym s1' ++
          [NTS lhs'] ++ FILTER isNonTmnlSym s2' ++
          FILTER isNonTmnlSym s1' ++ FILTER isNonTmnlSym rhs' ++
          FILTER isNonTmnlSym s2' ++
          FILTER isNonTmnlSym (FLAT t')))`
 by METIS_TAC [rmd_r2, rgr_r9eq, MEM, MEM_APPEND] THEN
METIS_TAC [MEM, NOT_CONS_NIL, LENGTH_NIL, DECIDE ``LENGTH l ≠ 0 ⇒ LENGTH l ≥ 1``]]);



val pumpCfg = store_thm
("pumpCfg",
``∀g.
   isCnf (g:('a,'b) grammar)  ⇒
   ∃n. n > 0 ∧
       ∀z. z ∈ language g ∧ LENGTH z ≥ n ⇒
           ∃u v w x y.
	     (z = u ++ v ++ w ++ x ++ y) ∧
             LENGTH v + LENGTH x ≥ 1 ∧
             LENGTH v + LENGTH w + LENGTH x ≤ n ∧
             ∀i. u++FLAT (lpow v i)++w++FLAT (lpow x i)++y ∈ language g``,

SRW_TAC [][] THEN
 Q.ABBREV_TAC `k=LENGTH (ntms g)` THEN
Q.EXISTS_TAC `2**k` THEN
SRW_TAC [][] THEN1 SRW_TAC [][Abbr`k`, GREATER_DEF] THEN
`z ∈ llanguage g` by METIS_TAC [drd_ld_langeq] THEN
`(lderives g)^* [NTS (startSym g)] z ∧ EVERY isTmnlSym z`
  by FULL_SIMP_TAC (srw_ss()) [llanguage_def] THEN
`∃dl.(lderives g) ⊢ dl ◁ [NTS (startSym g)] → z`
  by METIS_TAC [rtc2list_exists'] THEN
Q.ABBREV_TAC `k0=LENGTH (distinctldNts dl)` THEN
`LENGTH (distinctldNts dl) ≥ 1` by METIS_TAC [numdlds] THEN
`k0 ≥ 1 ⇒ 1 ≤ k0` by DECIDE_TAC THEN
`isNonTmnlSym (NTS (startSym g))` by METIS_TAC [isNonTmnlSym_def] THEN
IMP_RES_TAC dldntsLeg THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`MEM (startSym g) (ntms g)` by
(SRW_TAC [][ntms_def, ntList_def, nonTerminalsList_def] THEN
 METIS_TAC [rmd_r2, MEM, APPEND]) THEN
`k0 ≤ k` by METIS_TAC [dldntsLeg] THEN
 `1 ≤ k0` by METIS_TAC [] THEN
`k ≠ 0` by DECIDE_TAC THEN
 `LENGTH z ≥ 2 ** k0` by METIS_TAC [powGtTrans] THEN
 `LENGTH z > 2**(k0-1)` by METIS_TAC [powGt] THEN
 `symRepProp dl` by METIS_TAC [inpLeninv,symRepProp_def] THEN
`EVERY isNonTmnlSym ([NTS (startSym g)]:('a,'b) symbol list)`
by METIS_TAC [APPEND_ASSOC,APPEND_11,symbol_11,isNonTmnlSym_def,EVERY_DEF] THEN
 `∃pz0:('a,'b) symbol list sz0:('a,'b) symbol list.([NTS (startSym g)]=pz0++sz0) ∧
	 EVERY isTmnlSym pz0 ∧ EVERY isNonTmnlSym sz0`
 by METIS_TAC [EVERY_DEF,APPEND_NIL] THEN
`lastExpProp (g,dl,z)`
by METIS_TAC [lastExp,symbol_11] THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp] THEN
SRW_TAC [][] THEN
`lderives g ⊢ (dl1++TL dl2) ◁ [NTS N1]++[NTS N2] → (v++rst)` by
METIS_TAC [listderivTrans, APPEND] THEN
`∃pfx sfx.([NTS N1]++[NTS N2]=pfx++sfx) ∧ EVERY isTmnlSym pfx ∧
	 EVERY isNonTmnlSym sfx` by
(MAP_EVERY Q.EXISTS_TAC [`[]`,`[NTS N1]++[NTS N2]`] THEN
 SRW_TAC [][isNonTmnlSym_def]) THEN
`∃dl1' dl2' zb zy.
   splitDerivProp (g,dl1++TL dl2,v++rst)
   (dl1',[NTS N1],zb) (dl2',[NTS N2],zy)` by METIS_TAC [ldSplitDeriv,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
`LENGTH zb ≤ 2**(LENGTH (distinctldNts dl1') -1)`
by METIS_TAC [symRepProp_def, inpLen,EVERY_APPEND] THEN
`LENGTH zy ≤ 2**(LENGTH (distinctldNts dl2') -1)`
by METIS_TAC [symRepProp_def, inpLen,EVERY_APPEND] THEN
SRW_TAC [][] THEN
`∃v''.zb++zy=v++v''`by
(IMP_RES_TAC twoListAppEq THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
 METIS_TAC [APPEND_ASSOC]) THEN
SRW_TAC [][] THEN
`lderives g ⊢ MAP (listsec v []) dl2 ◁
   listsec v [] (v ++ ([NTS B]++w)) → listsec v [] (v ++ v'')`
by METIS_TAC [listsecldSfxNil,APPEND_ASSOC,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [listsecDropNilSfx] THEN
`¬symRepProp (MAP (listsec v []) dl2)` by METIS_TAC [notspropLsTmnls,
						    APPEND_ASSOC,
						    EVERY_APPEND] THEN
`MEM (v++[NTS B]++w) dl1` by
(Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 METIS_TAC [MEM, MEM_APPEND, APPEND_FRONT_LAST]) THEN
`v ++ [NTS B] ++ w = v ++ ([NTS B]++w)` by SRW_TAC [][] THEN
`∃p1 p2.([NTS B]++w = p1++p2) ∧ EVERY isTmnlSym p1 ∧ EVERY isNonTmnlSym p2`
by METIS_TAC [ldMemlderivesSfx] THEN
`∃dl1' dl2' zb' zy'.
   splitDerivProp (g,(MAP (listsec v []) dl2),v'') (dl1',[NTS B],zb')
   (dl2',w,zy')`
by METIS_TAC [APPEND,ldSplitDeriv] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`tsl`,`v`,`zb'`,`zy'`,`rst'`] THEN
SRW_TAC [][] THEN1
(FULL_SIMP_TAC (srw_ss()) [ntProp_def] THEN SRW_TAC [][]
 THENL[
       `LENGTH ([NTS B;NTS N2]) > 1` by
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
       `v ≠ [] ∨ w ≠ []` by METIS_TAC [cnfvwNotNil] THEN1
       (`LENGTH v ≠ 0` by METIS_TAC [LENGTH_NIL] THEN DECIDE_TAC) THEN
       `p1 = []` by (Cases_on `p1` THEN SRW_TAC [][] THEN
		     Cases_on `h` THEN SRW_TAC [][] THEN
		     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,
					       isNonTmnlSym_def]) THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `zy' ≠ []` by METIS_TAC [cnfNotLderivesNilAllntms,
				EVERY_DEF, APPEND_NIL] THEN
       `LENGTH zy' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
       DECIDE_TAC,

       `LENGTH ([NTS N1;NTS N2]) > 1` by
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
       `v ≠ [] ∨ w ≠ []` by METIS_TAC [cnfvwNotNil] THEN1
       (`LENGTH v ≠ 0` by METIS_TAC [LENGTH_NIL] THEN DECIDE_TAC) THEN
       `p1 = []` by (Cases_on `p1` THEN SRW_TAC [][] THEN
		     Cases_on `h` THEN SRW_TAC [][] THEN
		     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,
					       isNonTmnlSym_def]) THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `zy' ≠ []` by METIS_TAC [cnfNotLderivesNilAllntms,
				EVERY_DEF, APPEND_NIL] THEN
       `LENGTH zy' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
       DECIDE_TAC])
THENL[
      `LENGTH (distinctldNts dl1') ≤
      LENGTH (distinctldNts (dl1 ++ TL dl2))` by METIS_TAC [distElemLen_def] THEN
      `LENGTH (distinctldNts dl2') ≤
      LENGTH (distinctldNts (dl1 ++ TL dl2))` by METIS_TAC [distElemLen_def] THEN
      `LENGTH (zb ++ zy) = LENGTH (v ++ zb' ++ zy')`
      by METIS_TAC [APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `dl2 ≠ []` by (Cases_on `dl2` THEN
		     FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
      `∀e. (MEM e dl1 ⇒ MEM (tsl ++ e ++ sfx) dl)
      ∧ (∀e. MEM e dl2 ⇒ MEM (tsl ++ e ++ sfx) dl) ⇒
      LENGTH (distinctldNts (dl1++TL dl2)) ≤ LENGTH (distinctldNts dl)` by
      METIS_TAC [dldntsLenLe, APPEND_NIL] THEN
      `∀e. (MEM e dl1 ⇒ MEM (tsl ++ e ++ sfx) dl)
      ∧ (∀e. MEM e dl2 ⇒ MEM (tsl ++ e ++ sfx) dl) ⇒
      LENGTH (distinctldNts (dl1++TL dl2)) ≤ k` by
      METIS_TAC [DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``] THEN
      FULL_SIMP_TAC (srw_ss()) [distElemLen_def] THEN
      `LENGTH (distinctldNts dl1') ≤ k`
      by METIS_TAC [DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``] THEN
      `LENGTH (distinctldNts dl2') ≤ k`
      by METIS_TAC [DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``] THEN
      `LENGTH zb ≤ 2 ** (k-1)` by METIS_TAC [powLe] THEN
      `LENGTH zy ≤ 2 ** (k-1)` by METIS_TAC [powLe] THEN
      `LENGTH zb + LENGTH zy ≤ 2**(k-1) + 2**(k-1)`by DECIDE_TAC THEN
       `LENGTH zb + LENGTH zy ≤ 2*2**(k-1)`by DECIDE_TAC THEN
       `LENGTH zb + LENGTH zy ≤ 2**(k-1+1)`by METIS_TAC [powMult] THEN
       `LENGTH dl > 1` by
       (SPOSE_NOT_THEN ASSUME_TAC THEN
	Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	SRW_TAC [][] THEN
	`EVERY isTmnlSym (pz0++sz0)` by METIS_TAC [EVERY_APPEND] THEN
	Cases_on `pz0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       `k0 ≥ 1` by METIS_TAC [dldntsGe1] THEN
       `k - 1 + 1 = k` by DECIDE_TAC THEN
       METIS_TAC [],

       FULL_SIMP_TAC (srw_ss()) [language_def,llanguage_def, EXTENSION] THEN
       SRW_TAC [][]
       THENL[
	     (* 3 subgoals *)

	     (* 1 *)
	     FULL_SIMP_TAC (srw_ss()) [ntProp_def] THEN
	     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	      (`(tsl ++ [NTS B] ++ sfx) = pz0++sz0`
	      by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	      `(tsl ++ [NTS B] ++ sfx = [NTS (startSym g)])`
	      by METIS_TAC [] THEN
	      FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [][] THEN

	      `(lderives g)^* [NTS (startSym g)] (pfx++sfx')`
	      by METIS_TAC [ldMemRel, APPEND, APPEND_NIL, APPEND_ASSOC] THEN

	      `dl1 ≠ []` by (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* (pfx++sfx') (v ++ [NTS (startSym g)] ++ w)`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl1'' ≠ []` by (Cases_on `dl1''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* [NTS (startSym g)] zb'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl2'' ≠ []` by (Cases_on `dl2''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* w zy'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN
	      `(lderives g)^* [NTS (startSym g)] (v ++ [NTS (startSym g)] ++ w)`
	      by METIS_TAC [RTC_RTC] THEN
	      `(lderives g)^* v v` by SRW_TAC [][] THEN
	      `(lderives g)^* [NTS (startSym g)]
	     (FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i))`
	      by METIS_TAC [rtcDerivesReplEnd] THEN
	      `rst' = []` by
	      (Cases_on `dl3`  THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	       SRW_TAC [][] THEN
	       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def]) THEN
	      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      `llanguage g = language g` by METIS_TAC [drd_ld_langeq] THEN
	      FULL_SIMP_TAC (srw_ss()) [language_def, llanguage_def, EXTENSION] THEN
	      METIS_TAC [EVERY_APPEND, islpowTmnl]) THEN

	     `h = pz0++sz0` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN

	      `(lderives g)^* [NTS (startSym g)] (tsl ++ pfx++sfx'++sfx)`
	      by METIS_TAC [ldMemRel, APPEND, APPEND_ASSOC] THEN

	      `dl1 ≠ []` by (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* (pfx++sfx') (v ++ [NTS B] ++ w)`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl1'' ≠ []` by (Cases_on `dl1''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* [NTS B] zb'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN


	      `dl3 ≠ []` by (Cases_on `dl3` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* sfx rst'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl2'' ≠ []` by (Cases_on `dl2''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* w zy'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN
	      `(lderives g)^* [NTS (startSym g)] (tsl ++ v ++ [NTS B] ++ w ++sfx)`
	      by METIS_TAC [RTC_RTC, rtc_lderives_same_append_left,
			    rtc_lderives_same_append_right, APPEND_ASSOC] THEN
	      `(lderives g)^* [NTS B] (pfx++sfx')` by
	      (`lderives g (tsl ++ [NTS B] ++ sfx)
	       (tsl ++ pfx ++ sfx' ++ sfx)`
	       by METIS_TAC [ldMemRel', APPEND, APPEND_ASSOC] THEN
	       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
	       SRW_TAC [][] THEN
	      `EVERY isNonTmnlSym [NTS lhs]` by SRW_TAC [][isNonTmnlSym_def] THEN
	       `(s1=tsl) ∧ ([NTS lhs] ++ s2 = [NTS B]++sfx)`
	       by METIS_TAC [symlistdiv3, NOT_CONS_NIL] THEN
	       FULL_SIMP_TAC (srw_ss()) [] THEN
	       SRW_TAC [][] THEN
	       `rhs = pfx++sfx'` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	       METIS_TAC [ldres1, RTC_RULES]) THEN
	      `(lderives g)^* [NTS B] (v ++ [NTS B] ++ w)`
	      by METIS_TAC [RTC_RTC] THEN
	      `(lderives g)^* v v` by SRW_TAC [][] THEN
	      `(lderives g)^* [NTS B]
                 (FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i))`
	      by METIS_TAC [rtcDerivesReplEnd] THEN
	      `llanguage g = language g` by METIS_TAC [drd_ld_langeq] THEN
	      FULL_SIMP_TAC (srw_ss()) [language_def, llanguage_def, EXTENSION] THEN
	      `(lderives g)^* (pz0++sz0) (tsl ++ [NTS B] ++sfx)`
	      by METIS_TAC [ldMemRel, APPEND, APPEND_ASSOC] THEN
	      `(lderives g)^* (pz0++sz0)
		 (tsl ++ (FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i)) ++ sfx)`
	      by METIS_TAC [EVERY_APPEND, islpowTmnl, RTC_RTC,
			    rtc_lderives_same_append_right,
			    rtc_lderives_same_append_left] THEN
	      `(lderives g)^*
		 (tsl ++ FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i) ++ sfx)
		 (tsl ++ FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i) ++ rst')`
	      by METIS_TAC [APPEND_ASSOC, EVERY_APPEND, islpowTmnl,
			    rtc_lderives_same_append_left] THEN
	      `(lderives g)^* (pz0++sz0)
		 (tsl ++ FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i) ++ rst')`
	      by METIS_TAC [RTC_RTC, APPEND_ASSOC] THEN
	      METIS_TAC [EVERY_APPEND, islpowTmnl]),

	      METIS_TAC [islpowTmnl],

	      METIS_TAC [islpowTmnl]
	      ]]);


val _ = export_theory();


