open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory markerTheory

open listLemmasTheory relationLemmasTheory
     grammarDefTheory pdaDefTheory symbolDefTheory gnfTheory
     containerLemmasTheory


open boolLemmasTheory

val _ = new_theory "pdaEqCfg"

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1
val _ = diminish_srw_ss ["list EQ"];

(*
Theorem 5.3 If L is a CFL, then there exists a PDA M such that
L=N(M), empty stack acceptance.
*)

val trans = Define
`trans q (rule l r) : (('b,'isym) symbol,('b,'isym)symbol,'state) trans =
    ((SOME (HD r), NTS l, q), q, TL r)`;

val grammar2pda = Define
`grammar2pda (g:('n,'t)grammar) (q: 'state) =
let ts = MAP (trans q)  (rules g)
    in
	<| start := q;  ssSym := (NTS (startSym g));
           next := ts;
           final := ([]:'state list) |>`;

val g2pPdaExists = store_thm
("g2pPdaExists",
``∀g.∃m.(m = grammar2pda g)``,
SRW_TAC [][]);


val pdaStartState = store_thm("pdaStartState",
``(grammar2pda g q).start = q``,
SRW_TAC [][grammar2pda, LET_THM]);


val pdaStackSym = store_thm("pdaStackSym",
``(grammar2pda g q).ssSym = (NTS (startSym g))``,
SRW_TAC [][grammar2pda, LET_THM]);


val notNoneTrans = store_thm
("notNoneTrans",
``∀l q q'.¬(∃sym stk.trans q l = ((NONE, sym,q),q',stk))``,
SRW_TAC [][] THEN
Cases_on `l` THEN SRW_TAC [][trans]);

val transStateEq = store_thm
("transStateEq",
``∀l q q'.(MEM ((h,h',q),q',sl') (MAP (trans q) l)) ∨
          (MEM ((h,h',q'),q,sl') (MAP (trans q) l))
      ⇒
      (q=q')``,

Induct_on `l` THEN SRW_TAC [][]
THENL[
      Cases_on `h''` THEN FULL_SIMP_TAC (srw_ss()) [trans],
      METIS_TAC [],
      Cases_on `h''` THEN FULL_SIMP_TAC (srw_ss()) [trans],
      METIS_TAC []
      ]);



(*
  (derives g)^* [NTS (startSym g)] x
    ------------------------------------
      0.  (ID (grammar2pda g (qs,qi,qf) x0))^*
            (qs,x,[x0]) (state,[],[])
      1.  x0 ∉ nonTerminals g
*)


val transMemList = store_thm
("transMemList",
``∀l.MEM ((SOME h,h',q),q,sl) (MAP (trans q) l) ∧ EVERY validGnfProd l
       ⇒
    ∃nts.(h'=NTS nts) ∧ ∃ts.(h=TS ts) ∧ EVERY isNonTmnlSym sl ∧
			(MEM (rule nts (h::sl)) l)``,
Induct_on `l` THEN SRW_TAC [][]
THENL[
      Cases_on `h''` THEN Cases_on `l'` THEN
      FULL_SIMP_TAC (srw_ss()) [trans, validGnfProd_def] THEN
      SRW_TAC [][] THEN
      METIS_TAC [isTmnlSym_def],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      ]);

val transMemRule = store_thm
("transMemRule",
``MEM ((SOME h,h',q),q,sl) (grammar2pda g q).next ∧ isGnf g
     ⇒
    ∃nts.(h'=NTS nts) ∧ ∃ts.(h=TS ts) ∧ EVERY isNonTmnlSym sl ∧
			(MEM (rule nts (h::sl)) (rules g))``,
Cases_on `g` THEN SRW_TAC [][rules_def, isGnf_def, grammar2pda, LET_THM] THEN
METIS_TAC [transMemList]);

val idcImpEvTmnl = store_thm
("idcImpEvTmnl",
``∀dl sfx stk stk'.
     ID (grammar2pda g q) ⊢ dl ◁
        (q,pfx++sfx,stk) → (q,sfx,stk') ∧ isGnf g
              ⇒
	     EVERY isTmnlSym pfx``,

Induct_on `LENGTH pfx` THEN
SRW_TAC [][]
THENL[
      Cases_on `pfx` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [],

      Cases_on `pfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (arith_ss) [] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`TL pfx`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `v = LENGTH pfx - 1` by DECIDE_TAC THEN
      `0 < LENGTH pfx` by FULL_SIMP_TAC (arith_ss) [] THEN
      `v = LENGTH (TL pfx)` by METIS_TAC [LENGTH_TL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl=[]`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [rtc2list_def, listderiv_def],

	    Cases_on `dl` THEN SRW_TAC [][] THEN
	    Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  FULL_SIMP_TAC (srw_ss()) [rtc2list_def, listderiv_def] THEN
		  SRW_TAC [][] THEN
		  `LENGTH sfx = LENGTH pfx + LENGTH sfx`
		  by METIS_TAC [LENGTH_APPEND] THEN
		  FULL_SIMP_TAC (arith_ss) [],

		  Cases_on `h` THEN Cases_on `r` THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t` THEN SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
		  `<|start := q; ssSym := NTS (startSym g);
		  next := MAP (trans q) (rules g); final := []|> ⊢
		  (q,pfx ++ sfx,r') → h`
		  by FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM, ID_def] THEN
		  Cases_on `h` THEN Cases_on `r` THEN
		  Cases_on `pfx` THEN Cases_on `r'` THEN
		  FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
		  SRW_TAC [][]
		  THEN (TRY(
			FIRST_X_ASSUM (Q.SPECL_THEN
				       [`((q',t ++ sfx,sl' ++ t'')::t')`,
					`sfx`,`sl'++t''`, `stk'`] MP_TAC) THEN
			SRW_TAC [][] THEN
			`q'=q` by METIS_TAC [transStateEq] THEN
			SRW_TAC [][] THEN
			Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,
								    isGnf_def] THEN
			`∃nts.(h' = NTS nts) ∧ ∃ts.(h = TS ts) ∧
			EVERY isNonTmnlSym sl ∧ MEM (rule nts (h::sl)) l`
			by METIS_TAC [transMemList] THEN
			SRW_TAC [][isTmnlSym_def] )) THEN
			METIS_TAC [notNoneTrans, MEM_MAP]]]]);


val idlStateEq = store_thm
("idlStateEq",
``∀dl q q' inp inp' stk stk'.ID (grammar2pda g q) ⊢ dl ◁
             (q,inp,stk) → (q',inp',stk')
       ⇒
     (q = q')``,
HO_MATCH_MP_TAC list_INDUCT THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      Cases_on `inp` THEN Cases_on `stk` THEN
      FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM, ID_def] THEN
      METIS_TAC [notNoneTrans, MEM_MAP, transStateEq],

      Cases_on `h` THEN Cases_on `r` THEN
      Cases_on `inp` THEN Cases_on `stk` THEN
      FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM, ID_def] THEN
      METIS_TAC [transStateEq, notNoneTrans, MEM_MAP]
      ]);


val idInpLen = store_thm
("idInpLen",
``grammar2pda g q ⊢ (q,inp,stk) → (q',inp',stk')
	  ⇒
	 LENGTH inp' < LENGTH inp``,

Cases_on `inp` THEN Cases_on `stk` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM, ID_def] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [notNoneTrans, MEM_MAP]);

val idStateEq = store_thm
("idStateEq",
``grammar2pda g q ⊢ (q,inp,stk) → (q',inp',stk')
	  ⇒
	 (q=q')``,

Cases_on `inp` THEN Cases_on `stk` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM, ID_def] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [notNoneTrans, MEM_MAP, transStateEq]);

val idcInpLen = store_thm
("idcInpLen",
``∀dl q inp inp' stk stk'.ID (grammar2pda g q) ⊢ dl ◁
             (q,inp,stk) → (q,inp',stk') ∧ (LENGTH dl > 1)
       ⇒
       (LENGTH inp' < LENGTH inp)``,

HO_MATCH_MP_TAC list_INDUCT THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl=[]` THEN SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [],

      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `h` THEN Cases_on `r` THEN
      `LENGTH q'' < LENGTH inp` by METIS_TAC [idInpLen] THEN
      `q'=q` by METIS_TAC [idStateEq] THEN
      SRW_TAC [][] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (arith_ss) []]);



val idlStkEq = store_thm
("idlStkEq",
``∀dl q inp stk stk'.ID (grammar2pda g q) ⊢ dl ◁
             (q,inp,stk) → (q,inp,stk')
       ⇒
       (stk = stk')``,

SRW_TAC [][] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `LENGTH dl > 1` THEN1
(`LENGTH inp < LENGTH inp` by METIS_TAC [idcInpLen] THEN
FULL_SIMP_TAC (arith_ss) []) THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (arith_ss) [LENGTH] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]);


val idcImpLd = store_thm
("idcImpLd",
``∀dl sfx stk stk'.
     ID (grammar2pda g q) ⊢ dl ◁
        (q,pfx++sfx,stk) → (q,sfx,stk') ∧ isGnf g
              ⇒
	   (lderives g)^* stk (pfx++stk')``,

Induct_on `LENGTH pfx` THEN
SRW_TAC [][]
THENL[
      Cases_on `pfx` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [idlStkEq, RTC_REFL],

      Cases_on `pfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (arith_ss) [] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`TL pfx`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `v = LENGTH pfx - 1` by DECIDE_TAC THEN
      `0 < LENGTH pfx` by FULL_SIMP_TAC (arith_ss) [] THEN
      `v = LENGTH (TL pfx)` by METIS_TAC [LENGTH_TL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl=[]`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [rtc2list_def, listderiv_def],

	    Cases_on `dl` THEN SRW_TAC [][] THEN
	    Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  FULL_SIMP_TAC (srw_ss()) [rtc2list_def, listderiv_def] THEN
		  SRW_TAC [][] THEN
		  `LENGTH sfx = LENGTH pfx + LENGTH sfx`
		  by METIS_TAC [LENGTH_APPEND] THEN
		  FULL_SIMP_TAC (arith_ss) [],

		  Cases_on `h` THEN Cases_on `r` THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t` THEN SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
		  `<|start := q; ssSym := NTS (startSym g);
		  next := MAP (trans q) (rules g); final := []|> ⊢
		  (q,pfx ++ sfx,r') → h`
		  by FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM, ID_def] THEN
		  Cases_on `h` THEN Cases_on `r` THEN
		  Cases_on `pfx` THEN Cases_on `r'` THEN
		  FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
		  SRW_TAC [][]
		  THENL[
			FIRST_X_ASSUM (Q.SPECL_THEN
				       [`((q',t ++ sfx,sl' ++ t'')::t')`,
					`sfx`,`sl'++t''`, `stk'`] MP_TAC) THEN
			SRW_TAC [][] THEN
			`q'=q` by METIS_TAC [transStateEq] THEN
			SRW_TAC [][] THEN
			Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,
								    isGnf_def] THEN
			`∃nts.(h' = NTS nts) ∧ ∃ts.(h = TS ts) ∧
			EVERY isNonTmnlSym sl ∧ MEM (rule nts (h::sl)) l`
			by METIS_TAC [transMemList] THEN
			SRW_TAC [][] THEN
			`lderives (G l n) [NTS nts] (TS ts::sl)`
			by METIS_TAC [ldres1, rules_def] THEN
			`lderives (G l n) ([NTS nts]++t'') (TS ts::sl++t'')`
			by METIS_TAC [lderives_same_append_right, RTC_RTC] THEN
			`(lderives (G l n))^* (TS ts::sl ++ t'') (TS ts::t ++ stk')`
			by METIS_TAC [rtc_lderives_same_append_left, isTmnlSym_def,
				      APPEND, EVERY_DEF] THEN
			`(lderives (G l n))^* ([NTS nts]++t'') (TS ts::t++stk')`
			by METIS_TAC [RTC_RULES] THEN
			METIS_TAC [APPEND, APPEND_ASSOC],

			METIS_TAC [notNoneTrans, MEM_MAP],

			FIRST_X_ASSUM (Q.SPECL_THEN
				       [`((q',t ++ sfx,sl' ++ t'')::t')`,
					`sfx`,`sl'++t''`, `stk'`] MP_TAC) THEN
			SRW_TAC [][] THEN
			`q'=q` by METIS_TAC [transStateEq] THEN
			SRW_TAC [][] THEN
			Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,
								    isGnf_def] THEN
			`∃nts.(h' = NTS nts) ∧ ∃ts.(h = TS ts) ∧
			EVERY isNonTmnlSym sl ∧ MEM (rule nts (h::sl)) l`
			by METIS_TAC [transMemList] THEN
			SRW_TAC [][] THEN
			`lderives (G l n) [NTS nts] (TS ts::sl)`
			by METIS_TAC [ldres1, rules_def] THEN
			`lderives (G l n) ([NTS nts]++t'') (TS ts::sl++t'')`
			by METIS_TAC [lderives_same_append_right, RTC_RTC] THEN
			`(lderives (G l n))^* (TS ts::sl ++ t'') (TS ts::t ++ stk')`
			by METIS_TAC [rtc_lderives_same_append_left, isTmnlSym_def,
				      APPEND, EVERY_DEF] THEN
			`(lderives (G l n))^* ([NTS nts]++t'') (TS ts::t++stk')`
			by METIS_TAC [RTC_RULES] THEN
			METIS_TAC [APPEND, APPEND_ASSOC],

			METIS_TAC [notNoneTrans, MEM_MAP]
			]]]]);


val laesImpLang = store_thm
("laesImpLang",
``x ∈ laes (grammar2pda g q) ∧ isGnf g
         ⇒
       x ∈ language g``,

SRW_TAC [][language_def, laes_def] THEN
FULL_SIMP_TAC (srw_ss()) [pdaStackSym, pdaStartState] THEN
`∃dl. ID (grammar2pda g (q:'c)) ⊢ dl ◁
       ((q:'c),x,[NTS (startSym g)]) → (state,[],[])`
         by METIS_TAC [rtc2list_exists'] THEN
SRW_TAC [][] THEN
`state = q` by METIS_TAC [idlStateEq] THEN
 METIS_TAC [lderivesImpDerives, idcImpEvTmnl, idcImpLd, APPEND_NIL]);

(*
  ∃state.
      IDC (grammar2pda g (qs,qi,qf) x0)
        ((grammar2pda g (qs,qi,qf) x0).start,x,
         [(grammar2pda g (qs,qi,qf) x0).ssSym]) (state,[],[])
    ------------------------------------
      0.  (derives g)^* [NTS (startSym g)] x
      1.  EVERY isTmnlSym x
      2.  x0 ∉ nonTerminals g
*)



val gnfNotLastTmns =store_thm
("gnfNotLastTmns",
``∀x y.(lderives g)^* x y ⇒ (x=[NTS n]) ⇒ isGnf g
           ⇒
        ∀p s nts.((y = p++[NTS nts]++s) ⇒ EVERY isNonTmnlSym s)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      FULL_SIMP_TAC (srw_ss()) [lreseq],

      `∀p s nts.(y = p ++ [NTS nts] ++ s) ⇒
      EVERY isNonTmnlSym s` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
      SRW_TAC [][] THEN
      Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [isGnf_def, rules_def] THEN
      `validGnfProd (rule lhs rhs)`by METIS_TAC [EVERY_APPEND, EVERY_DEF,
						 rgr_r9eq] THEN
      FULL_SIMP_TAC (srw_ss()) [validGnfProd_def] THEN
      SRW_TAC [][] THEN
      `MEM (NTS nts) (s1 ++ ts::ntsl ++ s2)` by METIS_TAC [MEM_APPEND, MEM] THEN
      FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
      SRW_TAC [][]
      THENL[
	    FIRST_X_ASSUM (Q.SPECL_THEN [`r1'`, `r2'++[NTS lhs]++s2`,`nts`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`s1`, `s2`,`lhs`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `s=[]` THEN SRW_TAC [][] THEN
	    `s1 ++ ts::(r1' ++ [NTS nts] ++ r2') ++ s2 =
	    s1 ++ [ts]++(r1' ++ [NTS nts] ++ r2' ++ s2)`
	    by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	    `∃l1 l2.
	    (p++[NTS nts] = s1 ++ [ts] ++ l1) ∧ (s = l2) ∧
	    (r1' ++ [NTS nts] ++ r2' ++ s2 = l1 ++ l2) ∨
	    (s = l2 ++ [ts] ++ (r1' ++ [NTS nts] ++ r2' ++ s2)) ∧
	    (p++[NTS nts] = l1) ∧
	    (s1 = l1 ++ l2)` by METIS_TAC [list_r6] THEN
	    SRW_TAC [][] THEN1
	    (`EVERY isNonTmnlSym (r1' ++ [NTS nts] ++ r2' ++ s2)`
	    by FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [EVERY_APPEND]) THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

 	    FIRST_X_ASSUM (Q.SPECL_THEN [`s1`, `r1'++[NTS nts]++r2'`,`lhs`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    Cases_on `s=[]` THEN SRW_TAC [][] THEN
	    `s1 ++ ts::ntsl++(r1' ++ [NTS nts] ++ r2') =
	    s1 ++ [ts]++(ntsl++r1' ++ [NTS nts] ++ r2')`
	    by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	    `p++[NTS nts]++s = (p++[NTS nts])++s` by METIS_TAC [APPEND_ASSOC] THEN
	    `∃l1 l2.
	    (p++[NTS nts] = s1 ++ [ts] ++ l1) ∧ (s = l2) ∧
	    (ntsl ++ r1' ++ [NTS nts] ++ r2' = l1 ++ l2) ∨
	    (s = l2 ++ [ts] ++ (ntsl ++ r1' ++ [NTS nts] ++ r2')) ∧
	    (p++[NTS nts] = l1) ∧
	    (s1 = l1 ++ l2)` by METIS_TAC [list_r6] THEN
	    SRW_TAC [][] THEN1
	    (`EVERY isNonTmnlSym (ntsl ++ r1' ++ [NTS nts] ++ r2')`
	    by FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [EVERY_APPEND]) THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
	    ]]);


val ldImpIdc = store_thm
("ldImpIdc",
``∀dl x y.lderives g ⊢ dl ◁  [NTS (startSym g)] → (x++y) ∧
      isGnf g ∧ EVERY isTmnlSym x ∧ EVERY isNonTmnlSym y
              ⇒
	  RTC (ID (grammar2pda g q))
	  (q,x,[NTS (startSym g)]) (q,[],y)``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND] THEN
Cases_on `dl=[]` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      Cases_on `x'` THEN Cases_on `y` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def],

      Cases_on `dl` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
       FIRST_X_ASSUM (Q.SPECL_THEN [`[]`, `[NTS (startSym g)]`] MP_TAC) THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def, lreseq, isGnf_def] THEN
       SRW_TAC [][] THEN
       `validGnfProd (rule (startSym g) (x' ++ y))`
       by METIS_TAC [rgr_r9eq, EVERY_APPEND, EVERY_DEF] THEN
       FULL_SIMP_TAC (srw_ss()) [validGnfProd_def] THEN
       SRW_TAC [] [] THEN
       Q_TAC SUFF_TAC `ID (grammar2pda g q) (q,x',[NTS (startSym g)]) (q,[],y)` THEN1
       METIS_TAC [RTC_RULES] THEN
       FULL_SIMP_TAC (srw_ss()) [grammar2pda, LET_THM] THEN
       Cases_on `x'` THEN SRW_TAC [][ID_def] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][]
       THENL[
	    Cases_on `ts` THEN
	    FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def],

	    Cases_on `t` THEN Cases_on `h` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
	    SRW_TAC [] [],

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, trans] THEN
	    Cases_on `t` THEN Cases_on `h` THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [APPEND]
	    ],

       `t = FRONT t ++ [LAST t]` by METIS_TAC [APPEND_FRONT_LAST] THEN
       Cases_on `LAST t`
       THENL[
	     FIRST_X_ASSUM (Q.SPECL_THEN [`[]`, `[]`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     `rtc2list (lderives g) ([[]] ++ [x' ++ y])`
	     by METIS_TAC [rtc2list_distrib_append_snd, APPEND, APPEND_ASSOC,
			   NOT_CONS_NIL] THEN
	     FULL_SIMP_TAC (srw_ss()) [rtc2list_def, lderives_def],

	     `rtc2list (lderives g) ([h::t'] ++ [x' ++ y])`
	     by METIS_TAC [rtc2list_distrib_append_snd, APPEND, APPEND_ASSOC,
			   NOT_CONS_NIL] THEN
	     FULL_SIMP_TAC (srw_ss()) [rtc2list_def, lderives_def] THEN
	     Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [isGnf_def, rules_def,
							 startSym_def] THEN
	     `validGnfProd (rule lhs rhs)` by METIS_TAC [rgr_r9eq, EVERY_APPEND,
							 EVERY_DEF] THEN
	     FULL_SIMP_TAC (srw_ss()) [validGnfProd_def] THEN
	     SRW_TAC [][] THEN
	     `s1 ++ ts::ntsl ++ s2 = s1++[ts]++(ntsl++s2)` by METIS_TAC [APPEND,
							    APPEND_ASSOC] THEN
	     `∃l1 l2.
                (x' = s1 ++ [ts] ++ l1) ∧ (y = l2) ∧
		(ntsl++s2 = l1 ++ l2) ∨
		(y = l2 ++ [ts] ++ (ntsl++s2)) ∧ (x' = l1) ∧
		(s1 = l1 ++ l2)` by METIS_TAC [list_r6] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   Cases_on `ntsl` THEN Cases_on `l1` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][]
		   THENL[
			 FIRST_X_ASSUM (Q.SPECL_THEN [`s1`, `[NTS lhs]++l2`]
					MP_TAC) THEN
			 SRW_TAC [][] THEN
			 `rtc2list (lderives (G l n)) ([NTS n]::t)`
			 by METIS_TAC [rtc2list_distrib_append_fst, APPEND_ASSOC,
				       APPEND, NOT_CONS_NIL] THEN
			 `LAST ([NTS n]::t) = LAST t`
			 by METIS_TAC [last_append, APPEND] THEN
			 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
			 `IDC (grammar2pda (G l n) q) (q,s1,[NTS n])
			 (q,[],NTS lhs::l2)` by METIS_TAC [] THEN
			 `IDC (grammar2pda (G l n) q) (q,s1++[ts],[NTS n])
			 (q,[]++[ts],NTS lhs::l2)` by METIS_TAC [idcInpInsert] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Q_TAC SUFF_TAC `ID (grammar2pda (G l n) q)
			 (q,[ts],NTS lhs::l2) (q,[], l2)` THEN1
			 (SRW_TAC [][] THEN
			  METIS_TAC [ RTC_RULES_RIGHT1, APPEND_NIL]) THEN
			 SRW_TAC [][grammar2pda, LET_THM, ID_def, rules_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, trans] THEN
			 METIS_TAC [APPEND_NIL],

			 `rtc2list (lderives (G l n)) ([NTS n]::(FRONT t ++
			 [s1 ++ [NTS lhs] ++ h'::(t'' ++ l2)]))`
			 by METIS_TAC [rtc2list_distrib_append_fst, NOT_CONS_NIL,
				       APPEND_FRONT_LAST, APPEND_ASSOC,
				       APPEND] THEN
			 `(lderives (G l n))^* [NTS n]
			 (s1 ++ [NTS lhs] ++ h'::(t'' ++ l2))`
			 by METIS_TAC [rtc2listRtcHdLast, NOT_CONS_NIL, HD,
				       LAST_APPEND, LAST, NOT_CONS_NIL, APPEND] THEN
			 METIS_TAC [gnfNotLastTmns, EVERY_APPEND, EVERY_DEF,
				    sym_r1b, isGnf_def, APPEND, APPEND_ASSOC,rules_def],

			 FIRST_X_ASSUM (Q.SPECL_THEN [`s1`, `[NTS lhs]++s2`]
					MP_TAC) THEN
			 SRW_TAC [][] THEN
			 `rtc2list (lderives (G l n)) ([NTS n]::t)`
			 by METIS_TAC [rtc2list_distrib_append_fst, APPEND_ASSOC,
				       APPEND, NOT_CONS_NIL] THEN
			 `LAST ([NTS n]::t) = LAST t`
			 by METIS_TAC [last_append, APPEND] THEN
			 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
			 `IDC (grammar2pda (G l n) q) (q,s1,[NTS n])
			 (q,[],NTS lhs::s2)` by METIS_TAC [] THEN
			 `IDC (grammar2pda (G l n) q) (q,s1++[ts],[NTS n])
			 (q,[]++[ts],NTS lhs::s2)` by METIS_TAC [idcInpInsert] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Q_TAC SUFF_TAC `ID (grammar2pda (G l n) q)
			 (q,[ts],NTS lhs::s2) (q,[], NTS s::t''++s2)` THEN1
			 (SRW_TAC [][] THEN
			  METIS_TAC [ RTC_RULES_RIGHT1]) THEN
			 SRW_TAC [][grammar2pda, LET_THM, ID_def, rules_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, trans] THEN
			 METIS_TAC [APPEND_NIL],

			 Cases_on `h'` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def]
			 ],

		   Cases_on `ntsl` THEN Cases_on `l1` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   (Cases_on `ts` THEN FULL_SIMP_TAC (srw_ss())
		    [isNonTmnlSym_def,isTmnlSym_def])]]]]);



val langImpLaes = store_thm
("langImpLaes",
``x ∈ language g ∧  isGnf g
       ⇒
    x ∈ laes (grammar2pda g q)``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [laes_def, language_def] THEN
`(lderives g)^* [NTS (startSym g)] x` by METIS_TAC [derivesImpLderives] THEN
`∃dl.lderives g ⊢ dl ◁ [NTS (startSym g)] → x` by METIS_TAC [rtc2list_exists'] THEN
FULL_SIMP_TAC (srw_ss()) [pdaStartState, pdaStackSym] THEN
METIS_TAC [ldImpIdc, APPEND_NIL, EVERY_DEF]);


val thm5_3 = store_thm
("thm5_3",
 ``∀g:('nts, 'ts) grammar.isGnf g
         ⇒
       ∃(m:(('nts, 'ts) symbol, ('nts, 'ts) symbol, 'state) pda).
            (∀x. x ∈ language g = x ∈ laes m)``,

SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
Q.EXISTS_TAC `grammar2pda g q`  THEN
SRW_TAC [][] THEN
METIS_TAC [langImpLaes, laesImpLang]);


(*
Theorem 5.4 If L is N(M) for some PDA M, then L is a CFL.
*)

val adj = Define
`adj (NTS (q,e,q')) (NTS (r,e',r')) = (q'=r)`;

val transSym = Define
`transSym (NTS (st,sym,st')) = sym`;

val toState = Define
`toState (NTS (st,sym,st')) = st'`;

val frmState = Define
`frmState (NTS (st,sym,st')) =  st`;

val ntslCond = Define
`ntslCond m (q',ql) ntsl =
      EVERY isNonTmnlSym ntsl ∧
      (∀e1 e2 p s.(ntsl = p++[e1;e2]++s) ⇒ adj e1 e2) ∧
      (frmState (HD ntsl) = q') ∧
      (toState (LAST ntsl) = ql) ∧
      (∀e.MEM e ntsl ⇒ MEM (toState e) (statesList m)) ∧
      (∀e.MEM e ntsl ⇒ MEM (frmState e) (statesList m))`;


val p2gRules = Define
`p2gRules m =
{ rule (q,A,q1) [] | ((NONE,A,q),q1,[]) ∈ m.next } ∪
{ rule (q,A,q1) [TS ts] | ((SOME (TS ts),A,q),q1,[]) ∈ m.next } ∪
{ rule (q,A,p) ([TS ts]++L) | L ≠ [] ∧
 ∃mrhs q1. ((SOME (TS ts),A,q),q1,mrhs) ∈ m.next ∧ ntslCond m (q1,p) L ∧
       (MAP transSym L = mrhs) ∧ p ∈ statesList m } ∪
{ rule (q,A,p) L | L ≠ [] ∧
 ∃mrhs q1. ((NONE,A,q),q1,mrhs) ∈ m.next ∧ ntslCond m (q1,p) L ∧
       (MAP transSym L = mrhs) ∧ p ∈ statesList m }`;

val p2gStartRules = Define
`p2gStartRules m s =
{ rule s [NTS (m.start,m.ssSym,q)] | q |  q ∈ statesList m  }`;


val pda2grammar = Define
`pda2grammar m g =
¬(pdastate (startSym g) ∈ statesList m) ∧
(set (rules g) = p2gStartRules m (startSym g) ∪ p2gRules m)`;

val finitep2gStartRules = store_thm
("finitep2gStartRules",
``FINITE (p2gStartRules m s)``,

SRW_TAC [][p2gStartRules] THEN
Q.MATCH_ABBREV_TAC `FINITE P` THEN
Q.ABBREV_TAC `f = \q. if q ∈ statesList m then {rule s [NTS (m.start,m.ssSym,q)]}
		      else {}` THEN
Q_TAC SUFF_TAC `P = BIGUNION (IMAGE f (set (statesList m)))`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	SRW_TAC [][]) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`f`, Abbr`P`]);


val finitentslComp = store_thm
("finitentslComp",
``FINITE { (q,A,p) | q ∈ statesList m ∧ p ∈ statesList m ∧
	  A ∈ stkSymsList m m.next }``,

SRW_TAC [][] THEN
Q.MATCH_ABBREV_TAC `FINITE P` THEN
Q.ABBREV_TAC `f = \q. if q ∈ statesList m then
 IMAGE (λ(A,p). (q,A,p)) { (A,p) | p ∈ statesList m ∧ A ∈ stkSymsList m m.next }
 else {}` THEN
Q_TAC SUFF_TAC `P = BIGUNION (IMAGE f (set (statesList m)))` THEN1
 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	SRW_TAC [][] THEN
	Q.MATCH_ABBREV_TAC `FINITE P1` THEN
	Q.ABBREV_TAC `h = \A. if A ∈ stkSymsList m m.next then
	IMAGE (λp. (q,A,p)) { p | p ∈ statesList m } else {}` THEN
	Q_TAC SUFF_TAC `P1 = BIGUNION (IMAGE h (set (stkSymsList m m.next)))`
	THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`h`] THEN
	       SRW_TAC [][] THEN
	       Q.MATCH_ABBREV_TAC `FINITE P2` THEN
	       Q.ABBREV_TAC `i = \p. if p ∈ statesList m then {p} else {}` THEN
	       Q_TAC SUFF_TAC `P2 = BIGUNION (IMAGE i (set (statesList m)))`
	       THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`i`] THEN
		      SRW_TAC [][]) THEN
	       ONCE_REWRITE_TAC [EXTENSION] THEN
	       SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
			boolSimps.CONJ_ss][EXISTS_rule,
					   Abbr`i`, Abbr`P2`]) THEN
	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`h`, Abbr`P1`]  THEN
	METIS_TAC []) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`f`, Abbr`P`] THEN
	METIS_TAC []);


val finiteDuo = store_thm
("finiteDuo",
`` FINITE { (A,p) | A ∈ stkSymsList m m.next ∧ p ∈ statesList m }``,

SRW_TAC [][] THEN
Q.MATCH_ABBREV_TAC `FINITE P1` THEN
 Q.ABBREV_TAC `h = \A. if A ∈ stkSymsList m m.next then
 IMAGE (λp. (A,p)) { p | p ∈ statesList m } else {}` THEN
 Q_TAC SUFF_TAC `P1 = BIGUNION (IMAGE h (set (stkSymsList m m.next)))`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`h`] THEN
	       SRW_TAC [][] THEN
	       Q.MATCH_ABBREV_TAC `FINITE P2` THEN
	       Q.ABBREV_TAC `i = \p. if p ∈ statesList m then {p} else {}` THEN
	       Q_TAC SUFF_TAC `P2 = BIGUNION (IMAGE i (set (statesList m)))`
	       THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`i`] THEN
		      SRW_TAC [][]) THEN
	       ONCE_REWRITE_TAC [EXTENSION] THEN
	       SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
			boolSimps.CONJ_ss][EXISTS_rule,
					   Abbr`i`, Abbr`P2`]) THEN
	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`h`, Abbr`P1`]  THEN
	METIS_TAC []);



val finitentslImage = store_thm
("finitentslImage",
``(ntslComp = { (q,A,p) | q ∈ statesList m ∧ p ∈ statesList m ∧
	  A ∈ stkSymsList m m.next }) ⇒
 FINITE { ntsl | ntsl ⊆ (IMAGE NTS ntslComp) }``,

METIS_TAC [IMAGE_FINITE, finitentslComp, FINITE_POW, POW_DEF]);


val finElemSet2List = store_thm
("finElemSet2List",
``∀s1. FINITE s1 ⇒ (∀e. e ∈ s1 ⇒ FINITE e) ⇒ (∃s2. IMAGE set s2 = s1)``,

HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][] THEN
`∃s2. IMAGE set s2 = s1` by METIS_TAC [] THEN
`∃l. (set l = e)` by METIS_TAC [listExists4Set] THEN
Q.EXISTS_TAC `l INSERT s2` THEN
SRW_TAC [][]);

val finitentslCond = store_thm
("finitentslCond",
``FINITE { ntsl | ntsl |  ntslCond m (q1,q2) ntsl ∧ (LENGTH ntsl = n) ∧
	          EVERY (λe. e ∈ stkSymsList m m.next) (MAP transSym ntsl) }``,

SRW_TAC [][ntslCond] THEN
Q.MATCH_ABBREV_TAC `FINITE P` THEN
Q.ABBREV_TAC `ntslComp = { (q,A,p) | q ∈ statesList m ∧ p ∈ statesList m ∧
			  A ∈ stkSymsList m m.next }` THEN
Q_TAC SUFF_TAC `P ⊆ { l | EVERY (λe. e ∈ (IMAGE NTS ntslComp)) l ∧
                          (LENGTH l = n)}` THEN1

 (SRW_TAC [][] THEN
  Q_TAC SUFF_TAC `FINITE {l | EVERY (λe. ∃x. (e = NTS x) ∧ x ∈ ntslComp) l ∧
 (LENGTH l = n)}` THEN1
  METIS_TAC [SUBSET_FINITE] THEN
  Q.MATCH_ABBREV_TAC `FINITE P1` THEN
  `FINITE ntslComp` by METIS_TAC [finitentslComp] THEN
  Q.ABBREV_TAC `S1 = { ntsl | ntsl ⊆ (IMAGE NTS ntslComp) }` THEN
  Q.ABBREV_TAC `p = (λe. ∃x. (e = NTS x) ∧ x ∈ ntslComp)` THEN

  `FINITE {x | p x}` by
  (SRW_TAC [][Abbr `p`] THEN
  Q.MATCH_ABBREV_TAC `FINITE P2` THEN
  Q_TAC SUFF_TAC `P2 = IMAGE NTS ntslComp` THEN
  SRW_TAC [][Abbr `P2`, Abbr `ntslComp`] THEN
  SRW_TAC [][IMAGE_DEF, EXTENSION]) THEN

  `FINITE {l | EVERY p l ∧ (LENGTH l ≤ n)}` by METIS_TAC [finite_length_limited] THEN
  `{l | EVERY p l ∧ LENGTH l ≤ n} = P1 ∪ {l | EVERY p l ∧ LENGTH l < n}`
  by
  (SRW_TAC [][Abbr `P1`] THEN
  SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
  METIS_TAC [FINITE_UNION]) THEN

  UNABBREV_ALL_TAC THEN
  SRW_TAC [][EXTENSION, SUBSET_DEF] THEN
  `∀e. MEM e x ⇒ ∃e0.(e = NTS e0) ∧ ∃q A p. (e0=(q,A,p)) ∧
  q ∈ statesList m ∧ p ∈ statesList m ∧ A ∈ stkSymsList m m.next`
  by
(SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `e` THEN
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
 Cases_on `n` THEN
 Cases_on `r` THEN
 FULL_SIMP_TAC (srw_ss()) [transSym] THEN
 METIS_TAC [frmState, toState]) THEN
  SRW_TAC [][EVERY_MEM]);


val EXISTS_OPTION = store_thm(
  "EXISTS_OPTION",
  ``(?x:'a option. P x) <=> P NONE \/ (?x:'a. P (SOME x))``,
  EQ_TAC THEN1 (STRIP_TAC THEN Cases_on `x` THEN METIS_TAC []) THEN
  METIS_TAC []);

val EXISTS_symbol = store_thm(
  "EXISTS_symbol",
  ``(?x:('a,'b) symbol. P x) <=> (?x. P (TS x)) \/ (?x. P (NTS x))``,
  METIS_TAC [TypeBase.nchotomy_of ``:('a,'b)symbol``]);


val finitep2gRules = store_thm
("finitep2gRules",
``FINITE (p2gRules m)``,

SRW_TAC [][p2gRules]
THENL[
      Q.MATCH_ABBREV_TAC `FINITE P` THEN
      Q.ABBREV_TAC `f = \r:((δ, γ) symbol, β, α) trans.
      case r of
      ((isymo,A,q),q1,mrhs) =>
      if (isymo=NONE) ∧ (mrhs=[])
	  then {rule (q,A,q1) ([]:(α # β # α, γ) symbol list)}
      else {}` THEN
      Q_TAC SUFF_TAC `P = BIGUNION (IMAGE f (set m.next))`
      THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	     Cases_on `r` THEN
	     Cases_on `r'` THEN
	     Cases_on `q` THEN
	     Cases_on `r'` THEN
	     SRW_TAC [][]) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`f`, Abbr`P`] THEN
	SRW_TAC [][EQ_IMP_THM] THEN1
	(Q.EXISTS_TAC `((NONE,A,q),q1,[])` THEN
	SRW_TAC [][]) THEN
	Cases_on `r` THEN
	Cases_on `r'` THEN
	Cases_on `q` THEN
	Cases_on `r'` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `q''` THEN Cases_on `r` THEN
	FULL_SIMP_TAC (srw_ss()) [],

	(* TS case, similar to above *)

      Q.MATCH_ABBREV_TAC `FINITE P` THEN
      Q.ABBREV_TAC `f = \r:((δ, γ) symbol, β, α) trans.
      case r of
	  ((NONE,A,q),q1,mrhs) => {}
         | ((SOME (NTS t),A,q),q1,mrhs) => {}
         | ((SOME (TS ts),A,q),q1,mrhs) =>
         if (mrhs=[])
	  then {rule (q,A,q1) ([TS ts]:(α # β # α, γ) symbol list)}
	 else {}` THEN
      Q_TAC SUFF_TAC `P = BIGUNION (IMAGE f (set m.next))`
      THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	     Cases_on `r` THEN
	     Cases_on `r'` THEN
	     Cases_on `q` THEN
	     Cases_on `r'` THEN
	     SRW_TAC [][] THEN
	     Cases_on `q''` THEN SRW_TAC [][] THEN
	     Cases_on `x` THEN SRW_TAC [][]) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`f`, Abbr`P`] THEN
	SRW_TAC [][EQ_IMP_THM] THEN1
	(Q.EXISTS_TAC `((SOME (TS ts),A,q),q1,[])` THEN
	SRW_TAC [][]) THEN
	Cases_on `r` THEN
	Cases_on `r'` THEN
	Cases_on `q` THEN
	Cases_on `r'` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `q''` THEN Cases_on `r` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [],

	(* 3rd case *)
	Q.MATCH_ABBREV_TAC `FINITE P` THEN
	Q.ABBREV_TAC
	`f = \r:((δ, γ) symbol, β, α) trans.
	  case r of
            ((NONE,b1,b2),b3,b4) => ({}:(α # β # α, γ) rule -> bool)
          | ((SOME (NTS x1),x2,x3),x4,x5) => {}
	  | ((SOME (TS ts),A,q),q1,mrhs) =>
		  { rule (q,A,p) (TS ts::L) | L ≠ [] ∧
		   (MAP transSym L = mrhs) ∧
		   ntslCond m (q1,p) L ∧ p ∈ statesList m}` THEN
	Q_TAC SUFF_TAC `P = BIGUNION (IMAGE f (set m.next))` THEN1

	(DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	Cases_on `r` THEN
	Cases_on `r'` THEN
	Cases_on `q` THEN
	Cases_on `r'` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `q''` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

	Q.MATCH_ABBREV_TAC `FINITE P1` THEN
	Q.ABBREV_TAC `i: α -> (α # β # α, γ) rule -> bool =
        \p. {rule (r'',q,p) (TS t::L) | L |
        L ≠ [] ∧ ntslCond m (q',p) L ∧ (MAP transSym L = r) }` THEN
	Q_TAC SUFF_TAC `P1 = BIGUNION (IMAGE i (set (statesList m)))` THEN1

	 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`i`] THEN

	  Q.MATCH_ABBREV_TAC `FINITE P2` THEN
	Q.ABBREV_TAC `N:(α # β # α, γ) symbol list -> bool =
	{ntsl |
	 ntslCond m (q',p) ntsl ∧ (LENGTH ntsl = LENGTH r) ∧
	 EVERY (λe. e ∈ stkSymsList m m.next)
	 (MAP transSym ntsl)}` THEN
	Q.ABBREV_TAC `j = \e. rule (r'',q,p) (TS t::e)` THEN
	Q_TAC SUFF_TAC `P2 ⊆ IMAGE j N` THEN1
	  METIS_TAC [finitentslCond, IMAGE_FINITE, SUBSET_FINITE] THEN

	  SRW_TAC [][Abbr `P2`, Abbr `j`, Abbr `N`] THEN
	  SRW_TAC [][EXTENSION, EQ_IMP_THM, SUBSET_DEF] THEN
	SRW_TAC [][EVERY_MEM] THEN
	`e ∈ stkSyms m` by
	(SRW_TAC [][stkSyms_def] THEN
	METIS_TAC [mem_in]) THEN
	METIS_TAC [stkSyms_list_eqresult, mem_in]) THEN

	 ONCE_REWRITE_TAC [EXTENSION] THEN
	 SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		  boolSimps.CONJ_ss][EXISTS_rule,
				     Abbr`i`, Abbr`P1`] THEN
	 METIS_TAC []) THEN

	 ONCE_REWRITE_TAC [EXTENSION] THEN
	 SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		  boolSimps.CONJ_ss][EXISTS_rule,
				     Abbr`P`, Abbr`f`] THEN
         `∃q a p rhs. x = rule (q,a,p) rhs`
            by METIS_TAC [TypeBase.nchotomy_of ``:('a,'b)rule``,
                          pairTheory.pair_CASES] THEN
         SRW_TAC [][] THEN EQ_TAC THEN
         SIMP_TAC (srw_ss()) [pairTheory.EXISTS_PROD, EXISTS_OPTION,
                              EXISTS_symbol] THEN
         SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN METIS_TAC [],

	 (* final case *)
	 Q.MATCH_ABBREV_TAC `FINITE P` THEN
	Q.ABBREV_TAC
	`f = \r:((δ, γ) symbol, β, α) trans.
	  case r of
	      ((NONE,A,q),q1,mrhs) =>
	      { rule (q,A,p) L | L ≠ [] ∧
	       (MAP transSym L = mrhs) ∧
	       ntslCond m (q1,p) L ∧ p ∈ statesList m}
	    | ((SOME x,x2,x3),x4,x5) => ({}:(α # β # α, γ) rule -> bool)` THEN

	Q_TAC SUFF_TAC `P = BIGUNION (IMAGE f (set m.next))` THEN1

	(DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	Cases_on `r` THEN
	Cases_on `r'` THEN
	Cases_on `q` THEN
	Cases_on `r'` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `q''` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN

	Q.MATCH_ABBREV_TAC `FINITE P1` THEN
	Q.ABBREV_TAC `i: α -> (α # β # α, γ) rule -> bool =
        \p. {rule (r'',q,p) L | L |
        L ≠ [] ∧ ntslCond m (q',p) L ∧ (MAP transSym L = r) }` THEN
	Q_TAC SUFF_TAC `P1 = BIGUNION (IMAGE i (set (statesList m)))` THEN1

	 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`i`] THEN

	  Q.MATCH_ABBREV_TAC `FINITE P2` THEN
	Q.ABBREV_TAC `N:(α # β # α, γ) symbol list -> bool =
	{ntsl |
	 ntslCond m (q',p) ntsl ∧ (LENGTH ntsl = LENGTH r) ∧
	 EVERY (λe. e ∈ stkSymsList m m.next)
	 (MAP transSym ntsl)}` THEN
	Q.ABBREV_TAC `j = \e. rule (r'',q,p) e` THEN
	Q_TAC SUFF_TAC `P2 ⊆ IMAGE j N` THEN1
	  METIS_TAC [finitentslCond, IMAGE_FINITE, SUBSET_FINITE] THEN

	  SRW_TAC [][Abbr `P2`, Abbr `j`, Abbr `N`] THEN
	  SRW_TAC [][EXTENSION, EQ_IMP_THM, SUBSET_DEF] THEN
	SRW_TAC [][EVERY_MEM] THEN
	`e ∈ stkSyms m` by
	(SRW_TAC [][stkSyms_def] THEN
	METIS_TAC [mem_in]) THEN
	METIS_TAC [stkSyms_list_eqresult, mem_in]) THEN

	 ONCE_REWRITE_TAC [EXTENSION] THEN
	 SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		  boolSimps.CONJ_ss][EXISTS_rule,
				     Abbr`i`, Abbr`P1`] THEN
	 METIS_TAC []) THEN

	 ONCE_REWRITE_TAC [EXTENSION] THEN
	 SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		  boolSimps.CONJ_ss][EXISTS_rule,
				     Abbr`P`, Abbr`f`] THEN
         SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
                  [pairTheory.EXISTS_PROD, EXISTS_OPTION] THEN
         METIS_TAC []
	]);


val p2gGrExists = store_thm
("p2gGrExists",
``INFINITE (UNIV:δ set) ⇒
 ∀(m: ((α, β) symbol, γ, δ) pda) .
 ∃(g: (δ # γ # δ, β) grammar). pda2grammar m g``,

SRW_TAC [][pda2grammar] THEN
`FINITE (set (statesList m))` by SRW_TAC [][] THEN
`∃q. q ∉ (set (statesList m))` by METIS_TAC [new_state_exists] THEN

Q.ABBREV_TAC `R1:(δ # γ # δ, β) rule -> bool =
 (p2gStartRules m (q,sym,q1))` THEN
Q.ABBREV_TAC `R2 = (p2gRules m)` THEN

`FINITE R1` by METIS_TAC [finitep2gStartRules] THEN
`FINITE R2` by METIS_TAC [finitep2gRules] THEN

`∃r1. (set r1 = R1)` by METIS_TAC [listExists4Set] THEN
`∃r2. (set r2 =  R2)` by METIS_TAC [listExists4Set] THEN


Q.EXISTS_TAC `G (r1++r2) (q,sym,q1)` THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, rules_def, startSym_def, pdastate_def] THEN
METIS_TAC [mem_in]);


val tupfrmst = Define `tupfrmst (st,syms,stk,st') = st`;
val tuptost = Define `tuptost (st,syms,stk,st') = st'`;
val tupinp = Define `tupinp (st,syms,stk,st') = syms`;
val tupstk = Define `tupstk (st,syms,stk,st') = stk`;


val pdaTransSplit = store_thm
("pdaTransSplit",
``∀q qf inp stk.
     ID p ⊢ dl ◁ (q,inp,stk) → (qf,[],[])
       ⇒
      ∃l.(inp = FLAT (MAP tupinp l)) ∧
         (stk = MAP tupstk l) ∧
	 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList p)) ∧
	 (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList p)) ∧
	 (∀h t.(l=h::t) ⇒ (tupfrmst h = q) ∧ (tupstk h = HD stk) ∧
	  (tuptost (LAST l) = qf)) ∧
	 (∀e1 e2 pfx sfx.(l = pfx++[e1;e2]++sfx) ⇒
	  (tupfrmst e2 = tuptost e1) ∧
	  (∀e.MEM e l ⇒
	   ∃m.m < (LENGTH dl) ∧
	   NRC (ID p) m (tupfrmst e, tupinp e, [tupstk e])
	   (tuptost e,[],[])))``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `LENGTH dl < 2` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
(`(LENGTH dl = 0) ∨ (LENGTH dl = 1)` by DECIDE_TAC THEN1
 (`dl=[]` by METIS_TAC [LENGTH_NIL] THEN
 FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 Q.EXISTS_TAC `[]` THEN
 SRW_TAC [][]) THEN
IMP_RES_TAC ldIdcSplit
THENL[

      FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH dl1`] MP_TAC) THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`dl1`] MP_TAC) THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`q0`,`qf`,`i0`,`s0`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `(∃ipfx.inp=ipfx++FLAT(MAP tupinp l))` by METIS_TAC [idcInpSplit,
							   APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      `(stk≠[])` by
      (SPOSE_NOT_THEN ASSUME_TAC THEN
       SRW_TAC [][] THEN
       Cases_on `dl` THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       Cases_on `h'` THEN Cases_on `r` THEN
       FULL_SIMP_TAC (srw_ss()) [id_thm]) THEN
      `(∃spfx.MAP tupstk l=spfx++TL stk)` by METIS_TAC [idcStkLastSplit] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH (spfx++TL stk) = LENGTH stk - 1` by METIS_TAC [LENGTH_MAP] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `spfx=[]` by (Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [LENGTH_NIL]) THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `ipfx ++ FLAT (MAP tupinp l) = []` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
	    (* 3 subgoals *)

	     Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	     (FULL_SIMP_TAC(srw_ss()) [listderiv_def] THEN
	     Cases_on `dl` THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     Q.EXISTS_TAC `[(q,[],h,q0)]` THEN
	     SRW_TAC [][] THEN
	     SRW_TAC [][tupinp,tupstk,tupfrmst,tuptost] THEN
	      Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      `t'=[]` by METIS_TAC [rtc2listIdStkNil] THEN
	      SRW_TAC [][] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN1
	      (`LENGTH t ≠ 0` by DECIDE_TAC THEN
	       METIS_TAC [rtc2listLastMemState,LENGTH_NIL,pdastate_def,
			  APPEND,last_append]) THEN1
	      (`LENGTH t ≠ 0` by DECIDE_TAC THEN
	       METIS_TAC [rtc2listFstMemState,LENGTH_NIL]) THEN
	      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	    Q.EXISTS_TAC `(q,[],h,q0)::l`  THEN
	    SRW_TAC [][] THEN
	    SRW_TAC [][tupinp,tupstk,tupfrmst,tuptost]
	    THENL[
		  (* 8 subgoals *)

		  Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [rtc2listLastMemState,pdastate_def,last_append,APPEND],

		  Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [rtc2listFstMemState],

		  Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  SRW_TAC [][tuptost] THEN
		  METIS_TAC [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   `LENGTH ([h]++(MAP tupstk t ++ [tupstk e1; tupstk e2] ++
                   MAP tupstk sfx)) = SUC (LENGTH t + 2 + LENGTH sfx)`
		   by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		       FULL_SIMP_TAC (arith_ss) [])  THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   SUC (LENGTH t + 2 + LENGTH sfx) ≤ LENGTH (pdastk e)` by
		   (SRW_TAC [][] THEN Cases_on `e` THEN Cases_on `r` THEN
		    METIS_TAC [pdastk_def]) THEN
		   `ID p ⊢ dl0 ◁
		   (q,[]++[],
		    [h]++
		    (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
		     MAP tupstk sfx))
		   → (q0,[]++[],
		      []++(MAP tupstk t ++ [tupstk e1; tupstk e2] ++
		      MAP tupstk sfx))` by METIS_TAC [APPEND,APPEND_NIL] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
				     MAP tupstk sfx))`
		   by METIS_TAC [DECIDE ``SUC n = 1+n``,MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,[],[h]) → (q0,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL,APPEND] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN
		  `∃m.
		  m < LENGTH dl1 ∧
		  NRC (ID p) m
		  (tupfrmst e,tupinp e,[tupstk e])
		  (tuptost e,[],[])` by METIS_TAC [APPEND_NIL,rgr_r9eq,APPEND_ASSOC] THEN
		  `m < LENGTH dl` by DECIDE_TAC THEN
		  METIS_TAC [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   `LENGTH ([h]++(tupstk e2::MAP tupstk sfx)) =
		   SUC (SUC (LENGTH sfx))`
		   by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		   FULL_SIMP_TAC (arith_ss) []) THEN
		   `∀e.MEM e (FRONT dl0) ⇒ SUC (SUC (LENGTH sfx)) ≤
		   LENGTH (pdastk e)` by
		   (SRW_TAC [][] THEN
		    Cases_on `e` THEN Cases_on `r` THEN
		    METIS_TAC [pdastk_def]) THEN
		   `ID p ⊢ dl0 ◁
		   (q,[]++[],[h]++(tupstk e2::MAP tupstk sfx))
		   → (tupfrmst e2,[]++[],[]++(tupstk e2::MAP tupstk sfx))`
		   by METIS_TAC [APPEND_NIL,APPEND] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (tupstk e2::MAP tupstk sfx))`
		   by METIS_TAC [MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,[],[h]) → (tupfrmst e2,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL,APPEND] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN
		  `∃m.
		  m < LENGTH dl1 ∧
		  NRC (ID p) m
		  (tupfrmst e,tupinp e,[tupstk e])
		  (tuptost e,[],[])` by METIS_TAC [APPEND_NIL,rgr_r9eq,APPEND_ASSOC] THEN
		  `m < LENGTH dl` by DECIDE_TAC THEN
		  METIS_TAC [],


		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `sfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1 METIS_TAC [listderivNrc] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   FIRST_X_ASSUM (Q.SPECL_THEN [`e`,`h'`,`[]`,`t`] MP_TAC) THEN
		   SRW_TAC [][] THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		  METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``],


		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1
		   (FIRST_X_ASSUM (Q.SPECL_THEN [`e2`,`e`,`[]`,`t`] MP_TAC) THEN
		    SRW_TAC [][] THEN
		    METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		    METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``,APPEND_NIL,APPEND]) THEN
		  METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]
		  ],


	    Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN1
	    (
	     Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     `t=[]` by METIS_TAC [rtc2listIdStkNil] THEN
	     `LENGTH t = 0`by METIS_TAC [LENGTH_NIL] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     Q.EXISTS_TAC `[(q,ipfx,h,qf)]` THEN
	     SRW_TAC [][] THEN
	     SRW_TAC [][tupinp,tupstk,tupfrmst,tuptost] THEN1
	     (Cases_on `t'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      METIS_TAC [rtc2listLastMemState,pdastate_def,last_append,APPEND]) THEN1
	     (Cases_on `t'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      METIS_TAC [rtc2listFstMemState]) THEN
	     Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) []) THEN

	    Q.EXISTS_TAC `(q,ipfx,HD stk,q0)::l` THEN
	    SRW_TAC [][] THEN
	    SRW_TAC [][tupinp,tupstk,tupfrmst,tuptost]
	    THENL[
		  (* 9 subgoals *)

		  Cases_on `stk` THEN SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `t=[]` by METIS_TAC [LENGTH_NIL] THEN
		  SRW_TAC [][],

		  Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN METIS_TAC [rtc2listFstMemState]) THEN
		  METIS_TAC [rtc2listLastMemState,pdastate_def,last_append,APPEND],

		  Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN METIS_TAC [rtc2listFstMemState]) THEN
		  METIS_TAC [rtc2listFstMemState],


		  Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  SRW_TAC [][tuptost] THEN
		  METIS_TAC [],


		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `∀e.
		   MEM e (FRONT dl0) ⇒
		   SUC(LENGTH (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
			       MAP tupstk sfx)) ≤ LENGTH (pdastk e)`
		   by (FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `e` THEN Cases_on `r` THEN
		       METIS_TAC [pdastk_def]) THEN
		   `LENGTH ([h]++ (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
				   MAP tupstk sfx)) =
		   SUC(LENGTH(MAP tupstk t ++ [tupstk e1; tupstk e2] ++
			      MAP tupstk sfx))`
		   by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		       FULL_SIMP_TAC (arith_ss) []) THEN
		   `ID p ⊢ dl0 ◁(q,ipfx ++ FLAT
				 (MAP tupinp t ++ [tupinp e1; tupinp e2] ++
				  MAP tupinp sfx),
				 [h]++
				 (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
				  MAP tupstk sfx))
		   → (q0,[]++FLAT(MAP tupinp t ++
                        [tupinp e1; tupinp e2] ++
                        MAP tupinp sfx),
                     []++(MAP tupstk t ++ [tupstk e1; tupstk e2] ++
                     MAP tupstk sfx))` by METIS_TAC [APPEND_NIL,APPEND] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
                     MAP tupstk sfx))`
		   by METIS_TAC [MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,ipfx,[h]) → (q0,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN
		  `∃m.
		  m < LENGTH dl1 ∧
		  NRC (ID p) m
		  (tupfrmst e,tupinp e,[tupstk e])
		  (tuptost e,[],[])` by METIS_TAC [APPEND_NIL,rgr_r9eq,APPEND_ASSOC] THEN
		  `m < LENGTH dl` by DECIDE_TAC THEN
		  METIS_TAC [],


		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `∀e.
		   MEM e (FRONT dl0) ⇒
		   SUC (LENGTH (tupstk e2::MAP tupstk sfx)) ≤
		   LENGTH (pdastk e)`
		   by (FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `e` THEN Cases_on `r` THEN
		       METIS_TAC [pdastk_def]) THEN
		   `LENGTH ([h]++tupstk e2::MAP tupstk sfx) =
		  SUC (LENGTH (tupstk e2::MAP tupstk sfx))`
		  by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		      FULL_SIMP_TAC (arith_ss) []) THEN
		   `ID p ⊢ dl0 ◁
		   (q,ipfx ++ (tupinp e2 ++ FLAT (MAP tupinp sfx)),
		    [h]++(tupstk e2::MAP tupstk sfx))
		   → (tupfrmst e2,
		      []++(tupinp e2 ++ FLAT (MAP tupinp sfx)),
		      []++(tupstk e2::MAP tupstk sfx))`
		   by METIS_TAC [APPEND,APPEND_NIL,APPEND_ASSOC] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (tupstk e2::MAP tupstk sfx))`
		   by METIS_TAC [MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,ipfx,[h]) → (tupfrmst e2,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN
		  `∃m.
		  m < LENGTH dl1 ∧
		  NRC (ID p) m
		  (tupfrmst e,tupinp e,[tupstk e])
		  (tuptost e,[],[])` by METIS_TAC [APPEND_NIL,rgr_r9eq,APPEND_ASSOC] THEN
		  `m < LENGTH dl` by DECIDE_TAC THEN
		  METIS_TAC [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `sfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1 METIS_TAC [listderivNrc] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   FIRST_X_ASSUM (Q.SPECL_THEN [`e`,`h`,`[]`,`t`] MP_TAC) THEN
		   SRW_TAC [][] THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		  METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1
		   (FIRST_X_ASSUM (Q.SPECL_THEN [`e2`,`e`,`[]`,`t`] MP_TAC) THEN
		    SRW_TAC [][] THEN
		    METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``,APPEND_NIL,APPEND])
		  THEN
		  METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]
		  ],


	    Q.EXISTS_TAC `(q,ipfx,HD stk,q0)::l` THEN
	    SRW_TAC [][] THEN
	    SRW_TAC [][tupinp,tupstk,tupfrmst,tuptost]
	    THENL[
		  (* 9 subgoals *)
		  Cases_on `stk` THEN SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `t=[]` by METIS_TAC [LENGTH_NIL] THEN
		  SRW_TAC [][],

		  Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN METIS_TAC [rtc2listFstMemState]) THEN
		  METIS_TAC [rtc2listLastMemState,pdastate_def,last_append,APPEND],

		  Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN METIS_TAC [rtc2listFstMemState]) THEN
		  METIS_TAC [rtc2listFstMemState],

		  Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  SRW_TAC [][tuptost] THEN
		  METIS_TAC [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `∀e.MEM e (FRONT dl0) ⇒ SUC
		   (LENGTH (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
			    MAP tupstk sfx)) ≤ LENGTH (pdastk e)`
		   by (FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `e` THEN Cases_on `r` THEN
		       METIS_TAC [pdastk_def]) THEN
		   `LENGTH ([h]++
			    (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
			     MAP tupstk sfx)) = SUC
		   (LENGTH (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
			    MAP tupstk sfx))`
		   by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		       FULL_SIMP_TAC (arith_ss) []) THEN
		   `ID p ⊢ dl0 ◁
		   (q,ipfx ++FLAT(MAP tupinp t ++ [tupinp e1; tupinp e2] ++
				  MAP tupinp sfx),
		    [h]++(MAP tupstk t ++ [tupstk e1; tupstk e2] ++
			  MAP tupstk sfx))
		    → (q0,[]++FLAT(MAP tupinp t ++[tupinp e1; tupinp e2] ++
				   MAP tupinp sfx), []++(MAP tupstk t ++
							 [tupstk e1; tupstk e2] ++
							 MAP tupstk sfx))`
		    by METIS_TAC [APPEND,APPEND_NIL] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (MAP tupstk t ++ [tupstk e1; tupstk e2] ++
                     MAP tupstk sfx))`
		   by METIS_TAC [MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,ipfx,[h]) → (q0,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN
		  `∃m.m < LENGTH dl1 ∧ NRC (ID p) m (tupfrmst e,tupinp e,[tupstk e])
	    (tuptost e,[],[])` by METIS_TAC [APPEND_NIL,rgr_r9eq,APPEND_ASSOC] THEN
		  `m < LENGTH dl` by DECIDE_TAC THEN
		  METIS_TAC [],


		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN1
		  (IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `∀e.MEM e (FRONT dl0) ⇒ SUC
		   (LENGTH (tupstk e2::MAP tupstk sfx)) ≤ LENGTH (pdastk e)`
		   by (FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `e` THEN Cases_on `r` THEN
		       METIS_TAC [pdastk_def]) THEN
		   `LENGTH ([h]++
			    (tupstk e2::MAP tupstk sfx)) = SUC
		   (LENGTH (tupstk e2::MAP tupstk sfx))`
		   by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		       FULL_SIMP_TAC (arith_ss) []) THEN
		   `ID p ⊢ dl0 ◁
		   (q,ipfx ++(tupinp e2 ++ FLAT (MAP tupinp sfx)),
		    [h]++(tupstk e2::MAP tupstk sfx))
		    → (tupfrmst e2,[]++(tupinp e2++FLAT(MAP tupinp sfx)),
		       []++(tupstk e2::MAP tupstk sfx))`
		    by METIS_TAC [APPEND,APPEND_NIL,APPEND_ASSOC] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (tupstk e2::MAP tupstk sfx))`
		   by METIS_TAC [MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,ipfx,[h]) → (tupfrmst e2,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN1
		  (Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   SUC (LENGTH (tupstk e2::MAP tupstk sfx)) ≤ LENGTH (pdastk e)`
		   by (FULL_SIMP_TAC (srw_ss()) [] THEN
		       SRW_TAC [][] THEN
		       Cases_on `e` THEN Cases_on `r` THEN
		       METIS_TAC [pdastk_def]) THEN
		   `LENGTH ([h]++
			    (tupstk e2::MAP tupstk sfx)) = SUC
		   (LENGTH (tupstk e2::MAP tupstk sfx))`
		   by (FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN
		       FULL_SIMP_TAC (arith_ss) []) THEN
		   `ID p ⊢ dl0 ◁
		   (q,ipfx ++(tupinp e2 ++ FLAT (MAP tupinp sfx)),
		    [h]++(tupstk e2::MAP tupstk sfx))
		    → (tupfrmst e2,[]++(tupinp e2++FLAT(MAP tupinp sfx)),
		       []++(tupstk e2::MAP tupstk sfx))`
		    by METIS_TAC [APPEND,APPEND_NIL,APPEND_ASSOC] THEN
		   IMP_RES_TAC dlpropGen THEN
		   `∀e.MEM e (FRONT dl0) ⇒
		   ∃p. p ≠ [] ∧
		   (pdastk e = p ++ (tupstk e2::MAP tupstk sfx))`
		   by METIS_TAC [MEM] THEN
		   `∃dlx.LENGTH dlx ≤ LENGTH dl0 ∧
		   ID p ⊢ dlx ◁ (q,ipfx,[h]) → (tupfrmst e2,[],[])`
		   by METIS_TAC [pdaTransOnPfxLd,APPEND_NIL] THEN
		   `LENGTH dlx < LENGTH dl` by DECIDE_TAC THEN
		   METIS_TAC [listderivNrc]) THEN
		  `∃m.
		  m < LENGTH dl1 ∧
		  NRC (ID p) m
		  (tupfrmst e,tupinp e,[tupstk e])
		  (tuptost e,[],[])` by METIS_TAC [APPEND_NIL,rgr_r9eq,APPEND_ASSOC] THEN
		  `m < LENGTH dl` by DECIDE_TAC THEN
		  METIS_TAC [],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `sfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1 METIS_TAC [listderivNrc] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   FIRST_X_ASSUM (Q.SPECL_THEN [`e`,`h`,`[]`,`t`] MP_TAC) THEN
		   SRW_TAC [][] THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   Cases_on `sfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   FIRST_X_ASSUM (Q.SPECL_THEN [`e`,`h`,`[]`,`t`] MP_TAC) THEN
		   SRW_TAC [][] THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		  METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``],

		  Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   IMP_RES_TAC idcStkNil THEN
		   SRW_TAC [][] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1
		   (FIRST_X_ASSUM (Q.SPECL_THEN [`e2`,`e`,`[]`,`t`] MP_TAC) THEN
		    SRW_TAC [][] THEN
		    METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``,APPEND_NIL,APPEND]) THEN1
		  (SRW_TAC [][tuptost,tupfrmst,tupinp,tupstk] THEN
		   Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN1
		   (FIRST_X_ASSUM (Q.SPECL_THEN [`e2`,`e`,`[]`,`t`] MP_TAC) THEN
		    SRW_TAC [][] THEN
		    METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]) THEN
		   METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``,APPEND_NIL,APPEND])
		  THEN
		  METIS_TAC [DECIDE ``m < x ∧ x < y ⇒ m < y``]
		  ]],


      (* (q0,i0,s0) = (qf,[],[]) *)
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN1
      (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       `t=[]` by METIS_TAC [rtc2listIdStkNil] THEN
       FULL_SIMP_TAC (srw_ss()) []) THEN

      Q.EXISTS_TAC `[(q,inp,h,q0)]` THEN
      SRW_TAC [][] THEN
      SRW_TAC [][tupinp,tupstk,tupfrmst,tuptost]
      THENL[
	    `LENGTH t = 0`by DECIDE_TAC THEN
	    METIS_TAC [LENGTH_NIL],

	    Cases_on `dl0` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    SRW_TAC [][] THEN
	    Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `t''=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [rtc2listLastMemState,pdastate_def,last_append,APPEND],


	    Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    SRW_TAC [][] THEN
	    Cases_on `t'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [rtc2listFstMemState],

	    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [],

	    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [],

	    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [],

	    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [],

	    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) []
	    ]]);


val toRhs = Define
`toRhs (frm,inp,stk,tost) = NTS (frm,stk,tost)`;

val nextToStk = Define
`nextToStk ((a,b,c),d,e) = e`;

val toRhsLd = store_thm
("toRhsLd",
``∀l.(∀e.MEM e l ⇒
(derives g)^* [NTS (tupfrmst e,tupstk e,tuptost e)] (MAP toTmnlSym (tupinp e)))
  ⇒
  (derives g)^* (MAP toRhs l) (MAP toTmnlSym (FLAT (MAP tupinp l)))``,

Induct_on `l` THEN SRW_TAC [][] THEN
`(derives g)^* [NTS (tupfrmst h,tupstk h,tuptost h)]
  (MAP toTmnlSym (tupinp h))` by METIS_TAC [] THEN
 Cases_on `h` THEN
Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [tupinp,tupfrmst,tupstk,tuptost,toRhs] THEN
METIS_TAC [derives_append,APPEND]);


val nextMem2RuleNone = store_thm
("nextMem2RuleNone",
``MEM ((NONE,A,q),p,[]) m.next ⇒ pda2grammar m g
   ⇒
   MEM (rule (q,A,p) []) (rules g)``,

SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gRules, p2gStartRules] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
SRW_TAC [][]);


val ruleMem2nextMemNone = store_thm
("ruleMem2nextMemNone",
``MEM (rule (q,A,p) []) (rules g) ⇒ pda2grammar m g
   ⇒
  MEM ((NONE,A,q),p,[]) m.next``,

SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gRules, p2gStartRules] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION]);


val ruleMem2nextMemSome = store_thm
("ruleMem2nextMemSome",
``MEM (rule (q,A,p) [TS ih]) (rules g) ⇒ pda2grammar m g
   ⇒
  MEM ((SOME (TS ih),A,q),p,[]) m.next``,

SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gRules, p2gStartRules, EXTENSION, transSym,
			  ntslCond, isNonTmnlSym_def]);


val nextMem2RuleSome = store_thm
("nextMem2RuleSome",
``MEM ((SOME (TS s),A,q),p,[]) m.next ⇒ pda2grammar m g
    ⇒
    MEM (rule (q,A,p) [TS s]) (rules g)``,

SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gRules, EXTENSION, transSym,ntslCond,
			  isNonTmnlSym_def, p2gStartRules]);


open pairTheory;

val pdaTransListDerives = store_thm
("pdaTransListDerives",
``∀l.(∀e1 e2 pfx sfx.(l = pfx ++ [e1; e2] ++ sfx) ⇒(tupfrmst e2 = tuptost e1)) ∧
(∀e.MEM e l ⇒ (derives g)^* [NTS (tupfrmst e,tupstk e,tuptost e)]
              (tupinp e))
⇒
(derives g)^* (MAP toRhs l) (FLAT (MAP tupinp l))``,


Induct_on `l` THEN SRW_TAC [][] THEN
`(derives g)^* [NTS (tupfrmst h,tupstk h,tuptost h)]
              (tupinp h)` by METIS_TAC [] THEN

`(∀e1 e2 pfx sfx.
             (l = pfx ++ [e1; e2] ++ sfx) ⇒
             (tupfrmst e2 = tuptost e1))` by (SRW_TAC [][] THEN
Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND_NIL,APPEND]) THEN
`(derives g)^* (MAP toRhs l) (FLAT (MAP tupinp l))` by METIS_TAC [] THEN
Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
 FULL_SIMP_TAC (srw_ss()) [toRhs,tupinp,tuptost,tupfrmst,tupstk] THEN
METIS_TAC [derives_append,APPEND]);


val isAdj = store_thm
("isAdj",
``∀e1 e2 pfx sfx.(l = pfx ++ [e1; e2] ++ sfx) ⇒
 (tupfrmst e2 = tuptost e1) ⇒
 adj (toRhs e1) (toRhs e2)``,

Cases_on `l` THEN SRW_TAC [][] THEN
Cases_on `e1`  THEN
Cases_on `r` THEN Cases_on `r'` THEN
Cases_on `e2` THEN Cases_on `r'` THEN
Cases_on `r''` THEN
FULL_SIMP_TAC (srw_ss()) [adj,toRhs,tuptost,tupfrmst]);


val transSymtupStk = store_thm
("transSymtupStk",
``transSym (toRhs h) = tupstk h``,

Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [transSym,tupstk,toRhs]);


val maptransSymtupStk = store_thm
("maptransSymtupStk",
``∀l.MAP transSym (MAP toRhs l) = MAP tupstk l``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [transSym,tupstk,toRhs]);



val isNttoRhs = store_thm
("isNttoRhs",
``isNonTmnlSym (toRhs h)``,

Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [toRhs,isNonTmnlSym_def]);


val everyIsNttoRhs = store_thm
("everyIsNttoRhs",

``∀l.EVERY isNonTmnlSym (MAP toRhs l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [toRhs,isNonTmnlSym_def]);


val transFrmStEq = store_thm
("transFrmStEq",
 ``frmState (toRhs h) = tupfrmst h``,

Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [toRhs,frmState,tupfrmst]);




val transToStEq = store_thm
("transToStEq",
 ``toState (toRhs h) = tuptost h``,

Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [toRhs,toState,tuptost]);





val memMapToRhsSl = store_thm
("memMapToRhsSl",
``∀t.MEM e (MAP toRhs t) ∧
(∀e.MEM e (MAP tuptost t) ⇒ MEM e (statesList m)) ⇒
MEM (toState e) (statesList m)``,

Induct_on `t` THEN SRW_TAC [][] THEN
METIS_TAC [transToStEq]);

val memMapToRhsSl' = store_thm
("memMapToRhsSl'",
``∀t.MEM e (MAP toRhs t) ∧
(∀e.MEM e (MAP tupfrmst t) ⇒ MEM e (statesList m)) ⇒
MEM (frmState e) (statesList m)``,

Induct_on `t` THEN SRW_TAC [][] THEN
METIS_TAC [transFrmStEq]);


val isAdjList = store_thm
("isAdjList",
 ``∀t p s.
 (∀e1 e2 pfx sfx.(t = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1))
 ⇒ (MAP toRhs t = p ++ [e1; e2] ++ s) ⇒
 adj e1 e2``,

 Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN1
 (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  METIS_TAC [isAdj,APPEND_NIL,APPEND]) THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`t'`,`s`] MP_TAC) THEN SRW_TAC [][] THEN
 METIS_TAC [APPEND]);

val p2gtransNone = store_thm
("p2gtransNone",
``(LENGTH l ≥ 1) ∧ MEM ((NONE,A,q),q',MAP tupstk l) m.next ∧
 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList m)) ∧
  (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList m)) ∧
(∀h t.(l = h::t) ⇒(tupfrmst h = q') ∧ (tuptost (LAST (h::t)) = p)) ∧
(∀e1 e2 pfx sfx.(l = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1))
⇒
(rule (q,A,p) (MAP toRhs l)) ∈ p2gRules m``,

SRW_TAC [][p2gRules] THEN
DISJ2_TAC THEN
`l ≠ []` by (Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `q'` THEN
SRW_TAC [][maptransSymtupStk, ntslCond] THEN
SRW_TAC [][ntslCond,isNttoRhs,everyIsNttoRhs,transFrmStEq]
 THENL[

       Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [isAdjList,APPEND],

       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [transFrmStEq],

       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
       METIS_TAC [transToStEq,last_elem,APPEND,APPEND_ASSOC] THEN
       `t ≠ []` by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
       `t=FRONT t ++ [LAST t]`  by METIS_TAC [APPEND_FRONT_LAST] THEN
       ONCE_ASM_REWRITE_TAC [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [transToStEq,last_elem,APPEND,APPEND_ASSOC],

       METIS_TAC [memMapToRhsSl],

       METIS_TAC [memMapToRhsSl'],

       `l = FRONT l ++ [LAST l]` by METIS_TAC [APPEND_FRONT_LAST] THEN
       `∀e. e ∈ MAP tuptost ( FRONT l ++ [LAST l]) ⇒ e ∈ statesList m`
       by METIS_TAC [] THEN
       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []
      ]);



val p2gtransSome = store_thm
("p2gtransSome",
``(LENGTH l ≥ 1) ∧ MEM ((SOME (TS ih),A,q),q',MAP tupstk l) m.next ∧
 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList m)) ∧
  (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList m)) ∧
(∀h t.(l = h::t) ⇒(tupfrmst h = q') ∧ (tuptost (LAST (h::t)) = p)) ∧
(∀e1 e2 pfx sfx.(l = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1))
⇒
rule (q,A,p) (TS ih::(MAP toRhs l)) ∈ p2gRules m``,

SRW_TAC [][p2gRules] THEN
DISJ1_TAC THEN
DISJ2_TAC THEN
`l ≠ []` by (Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `q'` THEN
SRW_TAC [][maptransSymtupStk, ntslCond] THEN
SRW_TAC [][ntslCond,isNttoRhs,everyIsNttoRhs,transFrmStEq]
THENL[

       Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [isAdjList,APPEND],

       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [transFrmStEq],

       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
       METIS_TAC [transToStEq,last_elem,APPEND,APPEND_ASSOC] THEN
       `t=FRONT t ++ [LAST t]`  by METIS_TAC [APPEND_FRONT_LAST] THEN
       ONCE_ASM_REWRITE_TAC [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [transToStEq,last_elem,APPEND,APPEND_ASSOC],

       METIS_TAC [memMapToRhsSl],

       METIS_TAC [memMapToRhsSl'],

       `l = FRONT l ++ [LAST l]` by METIS_TAC [APPEND_FRONT_LAST] THEN
       `∀e. e ∈ MAP tuptost ( FRONT l ++ [LAST l]) ⇒ e ∈ statesList m`
       by METIS_TAC [] THEN
       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []
       ]);


val pdaImpP2g = store_thm
("pdaImpP2g",
``∀x q A p.
     ID m ⊢ dl ◁
        (q,x,[A]) → (p,[],[]) ∧ EVERY isTmnlSym x ∧
	pda2grammar m g
              ⇒
	   (derives g)^* [NTS (q,A,p)] x``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][]) THEN
 `ID m ⊢ h'::t' ◁ h' → (p,[],[])` by METIS_TAC [ldTl] THEN
 Cases_on `h'` THEN Cases_on `r` THEN
`(∃l.(q'' = FLAT (MAP tupinp l)) ∧
 (r' = MAP tupstk l) ∧
 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList m)) ∧
  (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList m)) ∧
 (∀h t. (l = h::t) ⇒ (tupfrmst h = q') ∧ (tupstk h = HD r') ∧
  (tuptost (LAST l) = p)) ∧
 (∀e1 e2 pfx sfx. (l = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1) ∧
  (∀e.MEM e l ⇒ ∃n.n < LENGTH ((q',q'',r')::t') ∧
  NRC (ID m) n (tupfrmst e,tupinp e,[tupstk e]) (tuptost e,[],[]))))`
 by METIS_TAC [pdaTransSplit] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 `t'=[]` by METIS_TAC [rtc2listIdStkNil] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
 SRW_TAC [][] THEN1
 (`MEM (rule (q,A,p) []) (rules g)`
  by METIS_TAC [nextMem2RuleNone] THEN
  METIS_TAC [res1, RTC_RULES]) THEN
 FULL_SIMP_TAC (srw_ss()) [ts2str_def, isTmnlSym_def] THEN
 `MEM (rule (q,A,p) [ih]) (rules g)`
 by METIS_TAC [nextMem2RuleSome] THEN
 METIS_TAC [res1, RTC_RULES]) THEN
Cases_on `LENGTH l = 1`  THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((tupfrmst h',tupinp h',
				       [tupstk h'])::t')`]
	       MP_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`((tupfrmst h',tupinp h',
				[tupstk h'])::t')`]
	       MP_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
(`rule (q,A,tuptost h') [NTS (tupfrmst h',tupstk h',tuptost h')] ∈ rules g`
by
 (FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
  Q_TAC SUFF_TAC
  `rule (q,A,tuptost h') [NTS (tupfrmst h',tupstk h',tuptost h')] ∈
  p2gStartRules m (startSym g) ∪ p2gRules m` THEN SRW_TAC [][] THEN1
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  FULL_SIMP_TAC (srw_ss()) [p2gRules, EXTENSION, transSym,ntslCond,p2gStartRules,
			   toState,frmState] THEN1
  METIS_TAC [memStateRule] THEN
  SRW_TAC [][isNonTmnlSym_def] THEN
  DISJ2_TAC THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
 METIS_TAC [res1, RTC_RULES]) THEN


(`rule (q,A,tuptost h') (ih::[NTS (tupfrmst h',tupstk h',tuptost h')]) ∈ rules g`
by
 (FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
  Q_TAC SUFF_TAC
  `rule (q,A,tuptost h') (ih::[NTS (tupfrmst h',tupstk h',tuptost h')]) ∈
  p2gStartRules m (startSym g) ∪ p2gRules m` THEN SRW_TAC [][] THEN1
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  FULL_SIMP_TAC (srw_ss()) [p2gRules, EXTENSION, transSym,ntslCond,p2gStartRules,
			   toState,frmState] THEN1
  METIS_TAC [memStateRule] THEN1
  METIS_TAC [memStateRule] THEN
  SRW_TAC [][isNonTmnlSym_def] THEN
  DISJ1_TAC THEN
  Cases_on `ih` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
 METIS_TAC [res1, RTC_RULES,rtc_derives_same_append_left, APPEND])) THEN

`∀e.MEM e l ⇒ (derives g)^* [NTS (tupfrmst e,tupstk e,tuptost e)] (tupinp e)`
by
(SRW_TAC [][] THEN
 Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN1
 (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
  SRW_TAC [][] THEN
  `∃n.n < SUC (LENGTH t') ∧
  NRC (ID m) n (tupfrmst e,tupinp e,[tupstk e])
  (tuptost e,[],[])` by METIS_TAC [APPEND,APPEND_NIL,APPEND_ASSOC] THEN
  `n < SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
  IMP_RES_TAC nrcListExists THEN
  SRW_TAC [][] THEN
  `SUC n < SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`l`] MP_TAC) THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`tupinp e`,`tupfrmst e`,`tupstk e`,
			       `tuptost e`]
		 MP_TAC) THEN SRW_TAC [][] THEN
  `EVERY isTmnlSym (tupinp e)`
  by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      METIS_TAC [EVERY_APPEND,APPEND]) THEN
  METIS_TAC []) THEN

Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(`∃n.
 n < SUC (LENGTH t') ∧
 NRC (ID m) n (tupfrmst e,tupinp e,[tupstk e])
 (tuptost e,[],[])` by METIS_TAC [APPEND,APPEND_NIL,APPEND_ASSOC] THEN
`n <  SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
IMP_RES_TAC nrcListExists THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`l`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`tupinp e`,`tupfrmst e`,`tupstk e`,`tuptost e`]
	       MP_TAC) THEN SRW_TAC [][] THEN
`EVERY isTmnlSym (tupinp e)`
by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
    SRW_TAC [][] THEN
    METIS_TAC [EVERY_APPEND,APPEND]) THEN
METIS_TAC []) THEN

`∃n.
 n < SUC (LENGTH t') ∧
 NRC (ID m) n (tupfrmst e,tupinp e,[tupstk e])
 (tuptost e,[],[])` by METIS_TAC [APPEND,APPEND_NIL,APPEND_ASSOC] THEN
`n <  SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
IMP_RES_TAC nrcListExists THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`l`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`tupinp e`,`tupfrmst e`,`tupstk e`,`tuptost e`]
	       MP_TAC) THEN SRW_TAC [][] THEN
`EVERY isTmnlSym (tupinp e)`
by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [everyFlat]) THEN
METIS_TAC []) THEN

`(derives g)^* (MAP toRhs l) (FLAT (MAP tupinp l))`
by METIS_TAC [pdaTransListDerives] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][]
THENL[
      `LENGTH l ≥ 1` by (Cases_on `l` THEN
			 FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      `(rule (q,A,p) (MAP toRhs l)) ∈ p2gRules m`
      by METIS_TAC [p2gtransNone] THEN
      `MEM (rule (q,A,p) (MAP toRhs l)) (rules g)`
      by FULL_SIMP_TAC (srw_ss()) [pda2grammar, EXTENSION] THEN
      METIS_TAC [RTC_RULES,res1],


      `LENGTH l ≥ 1` by (Cases_on `l` THEN
			 FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `ih` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,
						   isTmnlSym_def] THEN
      `(rule (q,A,p) (TS t::(MAP toRhs l))) ∈ p2gRules m`
      by METIS_TAC [p2gtransSome, symbol_11] THEN
      `MEM (rule (q,A,p) (TS t::(MAP toRhs l))) (rules g)`
      by FULL_SIMP_TAC (srw_ss()) [pda2grammar, EXTENSION] THEN
      METIS_TAC [RTC_RULES,res1,rtc_derives_same_append_left,APPEND]
      ]);


val listPairImpIdc = store_thm
("listPairImpIdc",
``∀l.(∀e1 e2.MEM (e1,e2) l ⇒
   (ID m)^* (frmState e1,e2,[transSym e1])
   (toState e1,[],[])) ∧
 (∀e1 e2 p s.(MAP FST l = p ++ [e1; e2] ++ s) ⇒ adj e1 e2)
  ⇒ EVERY isNonTmnlSym (MAP FST l) ⇒

  (∀h1 h2 i1 i2 t.((l = (h1,h2)::t) ∧ (LAST l = (i1,i2)))
    ⇒
   (ID m)^* (frmState h1,h2++(FLAT (MAP SND t)),[transSym h1]++
	     (MAP transSym (MAP FST t)))
   (toState i1,[],[]))``,


Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`∀e1 e2 p s.(MAP FST l = p ++ [e1; e2] ++ s) ⇒ adj e1 e2`
by METIS_TAC [rgr_r9eq,APPEND_ASSOC,APPEND] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`(ID m)^*
            (frmState q,r ++ FLAT (MAP SND t),
             transSym q::MAP transSym (MAP FST t))
            (toState i1,[],[])` by METIS_TAC [] THEN

`adj h1 q` by METIS_TAC [APPEND,APPEND_ASSOC,APPEND_NIL] THEN
Cases_on `h1` THEN Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
Cases_on `n` THEN  Cases_on `r'` THEN
Cases_on `n'` THEN  Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [adj,toState,frmState,transSym] THEN
SRW_TAC [][] THEN
`(ID m)^* (q,h2,[q']) (q'',[],[])`
by METIS_TAC [toState,transSym,frmState] THEN
METIS_TAC [idcStackInsert,idcInpInsert,APPEND_NIL,APPEND,
	   APPEND_ASSOC,RTC_RTC]);


val p2gImpPda = store_thm
("p2gImpPda",
``∀q A p x.(derives g) ⊢ dl ◁ [NTS (q,A,p)] → x ∧ q ∈ statesList m ⇒
  EVERY isTmnlSym x ⇒ pda2grammar m g
    ⇒
    (ID m)^* (q,x,[A]) (p,[],[])``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
`derives g ⊢ h'::t' ◁ h' → x` by METIS_TAC [ldTl] THEN
Cases_on `h'` THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
      IMP_RES_TAC ruleMem2nextMemNone THEN
      `t'=[]` by (Cases_on `t'` THEN
		  FULL_SIMP_TAC (srw_ss()) [derives_def]) THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [id_thm, RTC_RULES,APPEND_NIL],

      FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
      FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
      `rule (q,A,p) (h''::t) ∈ p2gStartRules m (startSym g) ∪ p2gRules m`
      by METIS_TAC [mem_in] THEN
      FULL_SIMP_TAC (srw_ss()) [p2gRules, p2gStartRules] THEN
      SRW_TAC [][] THEN1
      METIS_TAC [memStateRule, pdastate_def] THEN1
      (FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ([TS ts]::t')`] MP_TAC) THEN
       `isWord [TS ts]`by SRW_TAC [][isTmnlSym_def] THEN
       `t' = []` by (Cases_on `t'` THEN
		     FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq]) THEN
       SRW_TAC [][id_thm])
      THENL[
	    (* ((SOME (TS ts),A,q),q1,MAP transSym t) ∈ m.next ∧ t ≠ [] *)

	    Q.ABBREV_TAC `x=LAST ((TS ts::t)::t')` THEN
	    `LENGTH ((TS s::t)::t')=SUC (LENGTH t')`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC rtc2listExistsLen THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `∃dl y.(x=TS ts::y) ∧
	    (derives g) ⊢ dl ◁ t → y ∧ (LENGTH dl ≤ LENGTH l)`
	    by METIS_TAC [ldStartTs,Abbrev_def] THEN
	    `m ⊢ (q,TS ts::y,[A]) → (q1,y,MAP transSym t)`
	    by SRW_TAC [][id_thm] THEN
	    `∃l0.
	    (t = MAP FST l0) ∧ (y = FLAT (MAP SND l0)) ∧
	    ∀a b.MEM (a,b) l0 ⇒
	    ∃dl0.LENGTH dl0 ≤ LENGTH dl ∧
	    derives g ⊢ dl0 ◁ [a] → b` by
	    METIS_TAC [listPairExistsLd] THEN
	    SRW_TAC [][] THEN

	    `∀e1 e2.MEM (e1,e2) l0 ⇒
	    (ID m)^* (frmState e1,e2,[transSym e1])
	    (toState e1,[],[])` by
	    (SRW_TAC [][] THEN
	     RES_TAC THEN
	     `LENGTH dl0 < SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH dl0`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`dl0`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [ntslCond] THEN
	     Cases_on `dl0` THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     Cases_on `e1`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	     (Cases_on `n` THEN
	      Cases_on `r` THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      `∃r1' r2'.(l0 =r1' ++[(NTS (q',q'',r'),
				     LAST ([NTS (q',q'',r')]::t))] ++r2')`
	      by METIS_TAC [rgr_r9eq] THEN
	      SRW_TAC [][] THEN
	      FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,frmState,
					toState,transSym] THEN
	      `q' ∈ statesList m` by METIS_TAC [frmState, MEM, MEM_APPEND] THEN
	      METIS_TAC [everyFlat]) THEN
	     `t=[]` by (Cases_on `t` THEN
			FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq]) THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,isNonTmnlSym_def]) THEN
	    FULL_SIMP_TAC (srw_ss()) [ntslCond] THEN
	    `∀i2 i1.(LAST l0 = (i1,i2)) ⇒
		     ∀t h2 h1.(l0 = (h1,h2)::t) ⇒
		     (ID m)^*
		     (frmState h1,h2 ++ FLAT (MAP SND t),
		      [transSym h1] ++ MAP transSym (MAP FST t))
		     (toState i1,[],[])`
	    by METIS_TAC [listPairImpIdc] THEN

	    Cases_on `l0=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    `l0=FRONT l0++[LAST l0]` by METIS_TAC [APPEND_FRONT_LAST] THEN
	    SRW_TAC [][] THEN
	    Cases_on `LAST l0` THEN
	    Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `h` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
	    Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  Cases_on `n`  THEN
		  Cases_on `r''` THEN
		  FULL_SIMP_TAC (srw_ss()) [toState] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [frmState,transSym,
					    toState] THEN1
		  METIS_TAC [RTC_RULES, MEM, MEM_APPEND, frmState] THEN
		  `LAST t = (NTS (q',q''',r'''),r)`
		  by METIS_TAC [last_append,APPEND,APPEND_ASSOC,MEM] THEN
		  `toState (LAST (q''::MAP FST t))= r'''`
		  by (`MAP FST t = MAP FST (FRONT t) ++
		      MAP FST [(NTS (q',q''',r'''),r)]`
		      by METIS_TAC [MAP_APPEND,APPEND_FRONT_LAST] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      METIS_TAC [toState,last_append,APPEND,
				 last_elem]) THEN
		  METIS_TAC [RTC_RULES],

		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
		  FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
		  `EVERY isNonTmnlSym (MAP FST (FRONT t++[(TS t'',r)]))`
		  by METIS_TAC [APPEND_FRONT_LAST,last_append,APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]
		  ],


	    (* MEM ((NONE,A,q),q',transSym h''::MAP transSym t) m.next *)

	    Q.ABBREV_TAC `x=LAST ((h''::t)::t')` THEN
	    `LENGTH ((h''::t)::t')=SUC (LENGTH t')`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC rtc2listExistsLen THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `m ⊢ (q,x,[A]) → (q1,x,transSym h''::MAP transSym t)`
	    by SRW_TAC [][id_thm] THEN
	    `∃l0.
	    (h''::t = MAP FST l0) ∧ (x = FLAT (MAP SND l0)) ∧
	    ∀a b.MEM (a,b) l0 ⇒
	    ∃dl0.LENGTH dl0 ≤ LENGTH l ∧
	    derives g ⊢ dl0 ◁ [a] → b` by
	    METIS_TAC [listPairExistsLd] THEN
	    SRW_TAC [][] THEN

	    `∀e1 e2.MEM (e1,e2) l0 ⇒
	    (ID m)^* (frmState e1,e2,[transSym e1])
	             (toState e1,[],[])` by
	    (SRW_TAC [][] THEN
	     RES_TAC THEN
	     `LENGTH dl0 < SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH dl0`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`dl0`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [ntslCond] THEN
	     Cases_on `dl0` THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN
	     Cases_on `e1`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	     (Cases_on `n` THEN
	      Cases_on `r` THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      `∃r1' r2'.(l0 =r1' ++[(NTS (q',q'',r'),
				     LAST ([NTS (q',q'',r')]::t''))] ++r2')`
	      by METIS_TAC [rgr_r9eq] THEN
	      SRW_TAC [][] THEN
	      FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,frmState,
					toState,transSym] THEN
	      METIS_TAC [everyFlat, MEM, MEM_APPEND,frmState]) THEN
	     `t''=[]` by (Cases_on `t''` THEN
			FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq]) THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `EVERY isNonTmnlSym (MAP FST r1'''' ++ [TS t'''] ++ MAP FST r2'''')`
	     by METIS_TAC [EVERY_DEF,EVERY_APPEND] THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]) THEN

	    FULL_SIMP_TAC (srw_ss()) [ntslCond] THEN
	    `∀i2 i1.(LAST l0 = (i1,i2)) ⇒
		     ∀t h2 h1.(l0 = (h1,h2)::t) ⇒
		     (ID m)^*
		     (frmState h1,h2 ++ FLAT (MAP SND t),
		      [transSym h1] ++ MAP transSym (MAP FST t))
		     (toState i1,[],[])`
	    by METIS_TAC [listPairImpIdc,EVERY_DEF] THEN

	    Cases_on `l0=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    `l0=FRONT l0++[LAST l0]` by METIS_TAC [APPEND_FRONT_LAST] THEN
	    SRW_TAC [][] THEN
	    Cases_on `LAST l0` THEN
	    Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `h` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
	    Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  Cases_on `n`  THEN
		  Cases_on `r''` THEN
		  FULL_SIMP_TAC (srw_ss()) [toState] THEN
		  Cases_on `t''=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

		  (SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) [frmState,transSym,
					     toState] THEN
		   METIS_TAC [RTC_RULES]) THEN
		  `LAST t'' = (NTS (q',q'',r'''),r)`
		  by METIS_TAC [last_append,APPEND,APPEND_ASSOC,MEM] THEN

		  `toState (LAST (h''::MAP FST t''))= r'''`
		  by (`MAP FST t'' = MAP FST (FRONT t'') ++
		      MAP FST [(NTS (q',q'',r'''),r)]`
		      by METIS_TAC [MAP_APPEND,APPEND_FRONT_LAST] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      METIS_TAC [toState,last_append,APPEND,
				 last_elem]) THEN
		  METIS_TAC [RTC_RULES],

		  FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
		  Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [frmState,transSym,toState] THEN
		  `EVERY isNonTmnlSym (MAP FST (h::t'''))`
		  by FULL_SIMP_TAC (srw_ss()) [] THEN
		  `EVERY isNonTmnlSym (MAP FST (FRONT (h::t''') ++[(TS t,r)]))`
		  by METIS_TAC [APPEND_FRONT_LAST,last_append,APPEND,MEM] THEN
		  FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]
		  ]]]);


val p2gEqPda = store_thm
("p2gEqPda",
``pda2grammar m g ∧  EVERY isTmnlSym x ⇒
 ((derives g)^* ([NTS (startSym g)]:(α # β # α, γ) symbol list)  x =
  ∃p.(ID m)^* (m.start,x,[m.ssSym]) (p,[],[]))``,

SRW_TAC [][EQ_IMP_THM]
THENL[
      `([NTS (startSym g)] = x) ∨
      (∃y. derives g [NTS (startSym g)] y ∧ (derives g)^* y x)`
      by METIS_TAC [RTC_CASES1] THEN1
      (SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def]) THEN

      FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
      `rule (startSym g) y ∈ p2gStartRules m (startSym g) ∪ p2gRules m`
      by METIS_TAC [mem_in] THEN
      FULL_SIMP_TAC (srw_ss()) [p2gRules, p2gStartRules] THEN
      SRW_TAC [][] THEN1
      (`pda2grammar m g` by FULL_SIMP_TAC (srw_ss()) [pda2grammar,
						     p2gRules, p2gStartRules] THEN
      `m.start ∈ statesList m` by SRW_TAC [][statesList_def] THEN
      METIS_TAC [rtc2list_exists', p2gImpPda]) THEN
      METIS_TAC [memStateRule, pdastate_def],

      SRW_TAC [][Once RTC_CASES1] THEN
      DISJ2_TAC THEN
      Q.EXISTS_TAC `[NTS (m.start,m.ssSym,p)]` THEN
      SRW_TAC [][] THEN1
      (`rule (startSym g) [NTS (m.start,m.ssSym,p)] ∈ rules g`
       by
       (FULL_SIMP_TAC (srw_ss()) [derives_def, pda2grammar] THEN
	Q_TAC SUFF_TAC
      `rule (startSym g) [NTS (m.start,m.ssSym,p)] ∈
	p2gStartRules m (startSym g) ∪ p2gRules m`  THEN1
	FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
	FULL_SIMP_TAC (srw_ss()) [p2gRules, p2gStartRules] THEN
	`m.start ∈ statesList m` by SRW_TAC [][statesList_def] THEN
	METIS_TAC [memState]) THEN
      METIS_TAC [res1]) THEN
      METIS_TAC [pdaImpP2g, rtc2list_exists']]);


val _ = export_theory ();

