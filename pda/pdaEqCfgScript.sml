open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory markerTheory

open listLemmasTheory relationLemmasTheory
     grammarDefTheory pdaDefTheory regexpTheory

val _ = new_theory "pdaEqCfg"

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

(*
Theorem 5.3 If L is a CFL, then there exists a PDA M such that
L=N(M), empty stack acceptance.
*)


val validGnfProd = Define `validGnfProd (rule l r) = 
    ∃ts ntsl.(r = ts::ntsl) ∧ isTmnlSym ts ∧ EVERY isNonTmnlSym ntsl`;

val isGnf = Define `isGnf g = EVERY validGnfProd (rules g)`;


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
      FULL_SIMP_TAC (srw_ss()) [trans, validGnfProd] THEN
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
Cases_on `g` THEN SRW_TAC [][rules_def, isGnf, grammar2pda, LET_THM] THEN
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
								    isGnf] THEN
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
								    isGnf] THEN
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
								    isGnf] THEN
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
FULL_SIMP_TAC (srw_ss()) [pdaStackSym, pdaStartState, IDC_def] THEN
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
      Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [isGnf, rules_def] THEN
      `validGnfProd (rule lhs rhs)`by METIS_TAC [EVERY_APPEND, EVERY_DEF,
						 rgr_r9eq] THEN
      FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
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
	  IDC (grammar2pda g q)
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
      FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, IDC_def, isTmnlSym_def],

      Cases_on `dl` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      `LAST [x] = x'++y` by METIS_TAC [last_append, APPEND, NOT_CONS_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] 
      THENL[
       FIRST_X_ASSUM (Q.SPECL_THEN [`[]`, `[NTS (startSym g)]`] MP_TAC) THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def, lreseq, isGnf] THEN
       SRW_TAC [][IDC_def] THEN
       `validGnfProd (rule (startSym g) (x' ++ y))` 
       by METIS_TAC [rgr_r9eq, EVERY_APPEND, EVERY_DEF] THEN
       FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
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
	     Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [isGnf, rules_def, 
							 startSym_def] THEN
	     `validGnfProd (rule lhs rhs)` by METIS_TAC [rgr_r9eq, EVERY_APPEND,
							 EVERY_DEF] THEN
	     FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
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
			 (q,[]++[ts],NTS lhs::l2)` by METIS_TAC [idcInpInsert, 
								 IDC_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Q_TAC SUFF_TAC `ID (grammar2pda (G l n) q) 
			 (q,[ts],NTS lhs::l2) (q,[], l2)` THEN1
			 (SRW_TAC [][] THEN
			  METIS_TAC [IDC_def, RTC_RULES_RIGHT1, APPEND_NIL]) THEN
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
				    sym_r1b, isGnf, APPEND, APPEND_ASSOC,rules_def],

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
			 (q,[]++[ts],NTS lhs::s2)` by METIS_TAC [idcInpInsert, 
								 IDC_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Q_TAC SUFF_TAC `ID (grammar2pda (G l n) q) 
			 (q,[ts],NTS lhs::s2) (q,[], NTS s::t''++s2)` THEN1
			 (SRW_TAC [][] THEN
			  METIS_TAC [IDC_def, RTC_RULES_RIGHT1]) THEN
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
            x ∈ language g = x ∈ laes m``,

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

val transToState = Define
`transToState (NTS (st,sym,st')) = st'`;

val transFrmState = Define
`transFrmState (NTS (st,sym,st')) =  st`;

val ntslCond = Define
`ntslCond m (q',ql,mrhs) ntsl = 
      EVERY isNonTmnlSym ntsl ∧
      (∀e1 e2 p s.(ntsl = p++[e1;e2]++s) ⇒ adj e1 e2) ∧
      (transFrmState (HD ntsl) = q') ∧
      (transToState (LAST ntsl) = ql) ∧
      (∀e.MEM e ntsl ⇒ MEM (transToState e) (statesList m m.next)) ∧
      (∀e.MEM e ntsl ⇒ MEM (transFrmState e) (statesList m m.next))`;

val p2gtrans = Define
`p2gtrans m (rule l ntsl) = 
   ∃isymo ssym q q' p mrhs.
        MEM q (statesList m m.next) ∧ MEM q' (statesList m m.next) ∧ 
	MEM p (statesList m m.next) ∧
        (MEM ((isymo, ssym, q),q',mrhs) m.next ∧ (l=(q,ssym,p))) ∧	
	(((ntsl=[]) ∧ (isymo=NONE) ∧ (q'=p) ∧ (mrhs=[])) ∨ 
	 (∃ts.(ntsl=[TS ts]) ∧ (isymo=SOME (TS ts)) ∧ (q'=p) ∧ (mrhs=[])) ∨
	(∃h t.((ntsl=h::t) ∧ (t≠[])) ∧ 
	 ((∃ts.(h=TS ts) ∧ (isymo=SOME (TS ts)) ∧ 
	   (MAP transSym t=mrhs) ∧ 
	   ntslCond m (q',p,mrhs) t) ∨
	  ((isymo=NONE) ∧ (MAP transSym ntsl=mrhs) ∧ 
	   ntslCond m (q',p,mrhs) ntsl))))`;


val pda2grammar = Define
`pda2grammar m g = 
   (∀q.MEM q (statesList m m.next) =
       MEM (rule (startSym g) [NTS (m.start,m.ssSym,q)]) (rules g)) ∧
   (∀r.MEM r (rules g) = p2gtrans m r)`;


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
	 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList p p.next)) ∧
	 (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList p p.next)) ∧
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


val nextMemRuleExistsNone = store_thm
("nextMemRuleExistsNone",
``MEM ((NONE,A,q),q',MAP tupstk l) m.next ∧ pda2grammar m g 
   ⇒
   ∃p mrhs.MEM (rule (q,A,p) mrhs) (rules g) ∧ (mrhs = MAP toRhs l)``,

 SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);


val nextMemRuleExistsSome = store_thm
("nextMemRuleExistsSome",
``MEM ((SOME ih,A,q),q',MAP tupstk l) m.next ∧ pda2grammar m g ∧
 LENGTH l > 1  
   ⇒
   ∃p ntsl.MEM (rule (q,A,p) ntsl) (rules g) ∧ 
   ∃h t.((ntsl = h::t) ∧ (t ≠ []) ∧ (h = ih) ∧ 
	 (MAP transSym t = MAP tupstk l) ∧ ntslCond m (q',p,MAP tupstk l) t)``,

 SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);


val nextMemRuleExistsSome1 = store_thm
("nextMemRuleExistsSome1",
``MEM ((SOME ih,A,q),q',[tupstk h]) m.next ∧ pda2grammar m g 
   ⇒
MEM (rule (q,A,q') [ih]) (rules g) ∧ 
(∃ntsl ts.(ntsl = [TS ts]) ∧ (isymo = SOME (TS ts)) ∧ (mrhs = [TS ts]))``,

 SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);


val nextMem2RuleNone = store_thm
("nextMem2RuleNone",
``MEM ((NONE,A,q),p,[]) m.next ⇒ pda2grammar m g
   ⇒
   MEM (rule (q,A,p) []) (rules g)``,

SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);

val ruleMem2nextMemNone = store_thm
("ruleMem2nextMemNone",
``MEM (rule (q,A,p) []) (rules g) ⇒ pda2grammar m g 
   ⇒
  MEM ((NONE,A,q),p,[]) m.next``,


SRW_TAC [][pda2grammar] THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);


val ruleMem2nextMemSome = store_thm
("ruleMem2nextMemSome",
``MEM (rule (q,A,p) [ih]) (rules g) ⇒ pda2grammar m g 
   ⇒
  MEM ((SOME ih,A,q),p,[]) m.next``,

SRW_TAC [][pda2grammar] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);


val nextMem2RuleSome = store_thm
("nextMem2RuleSome",
``MEM ((SOME ih,A,q),p,[]) m.next ⇒ pda2grammar m g 
    ⇒
    MEM (rule (q,A,p) [ih]) (rules g)``,

SRW_TAC [][pda2grammar] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
SRW_TAC [][] THEN
METIS_TAC [memStateRule]);



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
 ``transFrmState (toRhs h) = tupfrmst h``,

Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN 
FULL_SIMP_TAC (srw_ss()) [toRhs,transFrmState,tupfrmst]);




val transToStEq = store_thm
("transToStEq",
 ``transToState (toRhs h) = tuptost h``,

Cases_on `h` THEN Cases_on `r` THEN
Cases_on `r'` THEN 
FULL_SIMP_TAC (srw_ss()) [toRhs,transToState,tuptost]);



	    

val memMapToRhsSl = store_thm
("memMapToRhsSl",
``∀t.MEM e (MAP toRhs t) ∧
(∀e.MEM e (MAP tuptost t) ⇒ MEM e (statesList m m.next)) ⇒
MEM (transToState e) (statesList m m.next)``,

Induct_on `t` THEN SRW_TAC [][] THEN
METIS_TAC [transToStEq]);

val memMapToRhsSl' = store_thm
("memMapToRhsSl'",
``∀t.MEM e (MAP toRhs t) ∧
(∀e.MEM e (MAP tupfrmst t) ⇒ MEM e (statesList m m.next)) ⇒
MEM (transFrmState e) (statesList m m.next)``,

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
``(LENGTH l ≥ 2) ∧ MEM ((NONE,A,q),q',MAP tupstk l) m.next ∧
 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList m m.next)) ∧
  (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList m m.next)) ∧
(∀h t.(l = h::t) ⇒(tupfrmst h = q') ∧(tuptost (LAST (h::t)) = p)) ∧
(∀e1 e2 pfx sfx.(l = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1)) 
⇒
p2gtrans m (rule (q,A,p) (MAP toRhs l))``,

SRW_TAC [][p2gtrans] THEN
Q.EXISTS_TAC `NONE` THEN
Q.EXISTS_TAC `q'` THEN
Q.EXISTS_TAC `MAP tupstk l` THEN
SRW_TAC [][] THEN1
METIS_TAC [memStateRule] THEN1
METIS_TAC [memStateRule] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 `LAST (h::t) = LAST t` by METIS_TAC [last_append,APPEND] THEN
 `MEM (LAST t) t` by METIS_TAC [APPEND_FRONT_LAST,MEM,MEM_APPEND] THEN
 `MEM p (MAP tuptost t)` by 
 (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
  SRW_TAC [][] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  SRW_TAC [][] THEN
  METIS_TAC [MAP_APPEND,MAP,APPEND_NIL]) THEN
 METIS_TAC []) THEN
Cases_on `l=[]` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
`∃h t.l=h::t` by METIS_TAC [list_mem2] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [transSymtupStk,maptransSymtupStk] THEN
SRW_TAC [][ntslCond,isNttoRhs,everyIsNttoRhs,transFrmStEq] 
THENL[
      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN1
      (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [isAdj,APPEND_NIL,APPEND]) THEN
      METIS_TAC [isAdjList,APPEND],

      `t=FRONT t ++ [LAST t]`  by METIS_TAC [APPEND_FRONT_LAST] THEN
      ONCE_ASM_REWRITE_TAC [] THEN
      SRW_TAC [][] THEN
      METIS_TAC [transToStEq,last_elem,APPEND,APPEND_ASSOC],
      
      METIS_TAC [memStateRule,transToStEq,transFrmStEq],

      METIS_TAC [memMapToRhsSl],

      METIS_TAC [transFrmStEq],

      METIS_TAC [memMapToRhsSl']
      ]);



val p2gtransSome = store_thm
("p2gtransSome",
``(LENGTH l ≥ 2) ∧ MEM ((SOME ih,A,q),q',MAP tupstk l) m.next ∧
 isTmnlSym ih ∧
 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList m m.next)) ∧
  (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList m m.next)) ∧
(∀h t.(l = h::t) ⇒(tupfrmst h = q') ∧(tuptost (LAST (h::t)) = p)) ∧
(∀e1 e2 pfx sfx.(l = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1)) 
⇒
p2gtrans m (rule (q,A,p) (ih::(MAP toRhs l)))``,

SRW_TAC [][p2gtrans] THEN
Q.EXISTS_TAC `SOME ih` THEN
Q.EXISTS_TAC `q'` THEN
Q.EXISTS_TAC `MAP tupstk l` THEN
SRW_TAC [][] THEN1
METIS_TAC [memStateRule] THEN1
METIS_TAC [memStateRule] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 `LAST (h::t) = LAST t` by METIS_TAC [last_append,APPEND] THEN
 `MEM (LAST t) t` by METIS_TAC [APPEND_FRONT_LAST,MEM,MEM_APPEND] THEN
 `MEM p (MAP tuptost t)` by 
 (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
  SRW_TAC [][] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  SRW_TAC [][] THEN
  METIS_TAC [MAP_APPEND,MAP,APPEND_NIL]) THEN
 METIS_TAC []) THEN

Cases_on `l=[]` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Cases_on `ih` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`∃h t.l=h::t` by METIS_TAC [list_mem2] THEN
Cases_on `t'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [transSymtupStk,maptransSymtupStk] THEN
SRW_TAC [][ntslCond,isNttoRhs,everyIsNttoRhs,transFrmStEq] 
THENL[

      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN1
      (Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [isAdj,APPEND_NIL,APPEND]) THEN
      METIS_TAC [isAdjList,APPEND],


      `t'=FRONT t' ++ [LAST t']`  by METIS_TAC [APPEND_FRONT_LAST] THEN
      ONCE_ASM_REWRITE_TAC [] THEN
      SRW_TAC [][] THEN
      METIS_TAC [transToStEq,last_elem,APPEND,APPEND_ASSOC],
      
      METIS_TAC [memStateRule,transToStEq,transFrmStEq],

      METIS_TAC [memMapToRhsSl],

      METIS_TAC [transFrmStEq],

      METIS_TAC [memMapToRhsSl']
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
 (∀e.MEM e (MAP tuptost l) ⇒ MEM e (statesList m m.next)) ∧
  (∀e.MEM e (MAP tupfrmst l) ⇒ MEM e (statesList m m.next)) ∧
 (∀h t. (l = h::t) ⇒ (tupfrmst h = q') ∧ (tupstk h = HD r') ∧
  (tuptost (LAST l) = p)) ∧
 (∀e1 e2 pfx sfx. (l = pfx ++ [e1; e2] ++ sfx) ⇒ (tupfrmst e2 = tuptost e1) ∧
  (∀e.MEM e l ⇒ ∃n.n < LENGTH ((q',q'',r')::t') ∧ 
  NRC (ID m) n (tupfrmst e,tupinp e,[tupstk e]) (tuptost e,[],[]))))` 
 by METIS_TAC [pdaTransSplit] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `LENGTH l < 2`THEN1
(`(LENGTH l = 0) ∨ (LENGTH l = 1)` by DECIDE_TAC 
 THENL[
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `l=[]` by METIS_TAC [LENGTH_NIL] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
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
       METIS_TAC [res1, RTC_RULES],
       
       
       Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       `t=[]` by METIS_TAC [LENGTH_NIL] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((tupfrmst h',tupinp h',
					      [tupstk h'])::t')`]
		      MP_TAC) THEN
       SRW_TAC [][] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`((tupfrmst h',tupinp h',
				       [tupstk h'])::t')`]
		      MP_TAC) THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
       SRW_TAC [][] 
       THENL[
	     FIRST_X_ASSUM (Q.SPECL_THEN [`tuptost h'`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     Cases_on `h'` THEN
	     Cases_on `r` THEN
	     Cases_on `r'` THEN
	     FULL_SIMP_TAC (srw_ss()) [tupinp,tuptost,tupfrmst,tupstk] THEN
	     `MEM (rule (q,A,r) [NTS (q',q''',r)]) (rules g)` 
	     by (FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
		 FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
		 METIS_TAC [memStateRule]) THEN
	     METIS_TAC [res1,RTC_RULES],
	     
	     FIRST_X_ASSUM (Q.SPECL_THEN [`tuptost h'`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     Cases_on `h'` THEN
	     Cases_on `r` THEN
	     Cases_on `r'` THEN
	     FULL_SIMP_TAC (srw_ss()) [tupinp,tuptost,tupfrmst,tupstk] THEN
	     `MEM (rule (q,A,r) (ih::[NTS (q',q''',r)])) (rules g)` 
	     by (FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
		 FULL_SIMP_TAC (srw_ss()) [p2gtrans] THEN
		 METIS_TAC [memStateRule]) THEN
	     METIS_TAC [res1,RTC_RULES,rtc_derives_same_append_left,APPEND]]]) THEN
 
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
      `LENGTH l ≥ 2` by DECIDE_TAC THEN
      `p2gtrans m (rule (q,A,p) (MAP toRhs l))` 
      by METIS_TAC [p2gtransNone] THEN
      `MEM (rule (q,A,p) (MAP toRhs l)) (rules g)`
      by METIS_TAC [pda2grammar,p2gtrans] THEN
      METIS_TAC [RTC_RULES,res1],
      
		  
      `LENGTH l ≥ 2` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `p2gtrans m (rule (q,A,p) (ih::(MAP toRhs l)))` 
      by METIS_TAC [p2gtransSome] THEN
      `MEM (rule (q,A,p) (ih::(MAP toRhs l))) (rules g)`
      by METIS_TAC [pda2grammar,p2gtrans] THEN
      METIS_TAC [RTC_RULES,res1,rtc_derives_same_append_left,APPEND]
      ]);

	    
	    

val listPairImpIdc = store_thm
("listPairImpIdc",
``∀l.(∀e1 e2.MEM (e1,e2) l ⇒
   (ID m)^* (transFrmState e1,e2,[transSym e1])
   (transToState e1,[],[])) ∧
 (∀e1 e2 p s.(MAP FST l = p ++ [e1; e2] ++ s) ⇒ adj e1 e2) 
  ⇒ EVERY isNonTmnlSym (MAP FST l) ⇒

  (∀h1 h2 i1 i2 t.((l = (h1,h2)::t) ∧ (LAST l = (i1,i2)))
    ⇒
   (ID m)^* (transFrmState h1,h2++(FLAT (MAP SND t)),[transSym h1]++
	     (MAP transSym (MAP FST t)))
   (transToState i1,[],[]))``,


Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`∀e1 e2 p s.(MAP FST l = p ++ [e1; e2] ++ s) ⇒ adj e1 e2`
by METIS_TAC [rgr_r9eq,APPEND_ASSOC,APPEND] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`(ID m)^*
            (transFrmState q,r ++ FLAT (MAP SND t),
             transSym q::MAP transSym (MAP FST t))
            (transToState i1,[],[])` by METIS_TAC [] THEN

`adj h1 q` by METIS_TAC [APPEND,APPEND_ASSOC,APPEND_NIL] THEN
Cases_on `h1` THEN Cases_on `q` THEN 
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
Cases_on `n` THEN  Cases_on `r'` THEN
Cases_on `n'` THEN  Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [adj,transToState,transFrmState,transSym] THEN
SRW_TAC [][] THEN
`(ID m)^* (q,h2,[q']) (q'',[],[])`
by METIS_TAC [transToState,transSym,transFrmState] THEN
METIS_TAC [idcStackInsert,idcInpInsert,APPEND_NIL,APPEND,
	   APPEND_ASSOC,RTC_RTC]);


val p2gImpPda = store_thm
("p2gImpPda",
``∀q A p x.(derives g) ⊢ dl ◁ [NTS (q,A,p)] → x ⇒ 
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
      
      `∃isymo q' mrhs.
      MEM q (statesList m m.next) ∧
      MEM q' (statesList m m.next) ∧
      MEM p (statesList m m.next) ∧
      MEM ((isymo,A,q),q',mrhs) m.next ∧
      ((∃ts.
          ((h'' = TS ts) ∧ (t = [])) ∧
          (isymo = SOME (TS ts)) ∧ (q' = p) ∧
          (mrhs = [])) ∨
       t ≠ [] ∧
       ((∃ts.
           (h'' = TS ts) ∧ (isymo = SOME (TS ts)) ∧
           (MAP transSym t = mrhs) ∧
           ntslCond m (q',p,mrhs) t) ∨
        (isymo = NONE) ∧
        (transSym h''::MAP transSym t = mrhs) ∧
        ntslCond m (q',p,mrhs) (h''::t)))`
      by (FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
	  FULL_SIMP_TAC (srw_ss()) [pda2grammar] THEN
	  FULL_SIMP_TAC (srw_ss()) [p2gtrans]) THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
      
	    FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
	    `t'=[]` by (Cases_on `t'` THEN
			FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq]) THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [id_thm, RTC_RULES,APPEND_NIL],


	    Q.ABBREV_TAC `x=LAST ((TS ts::t)::t')` THEN
	    `LENGTH ((TS s::t)::t')=SUC (LENGTH t')`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC rtc2listExistsLen THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `∃dl y.(x=TS ts::y) ∧
	    (derives g) ⊢ dl ◁ t → y ∧ (LENGTH dl ≤ LENGTH l)` 
	    by METIS_TAC [ldStartTs,Abbrev_def] THEN
	    `m ⊢ (q,TS ts::y,[A]) → (q',y,MAP transSym t)` 
	    by SRW_TAC [][id_thm] THEN
	    `∃l0.
	    (t = MAP FST l0) ∧ (y = FLAT (MAP SND l0)) ∧
	    ∀a b.MEM (a,b) l0 ⇒
	    ∃dl0.LENGTH dl0 ≤ LENGTH dl ∧ 
	    derives g ⊢ dl0 ◁ [a] → b` by 
	    METIS_TAC [listPairExistsLd] THEN
	    SRW_TAC [][] THEN

	    `∀e1 e2.MEM (e1,e2) l0 ⇒ 
	    (ID m)^* (transFrmState e1,e2,[transSym e1]) 
	             (transToState e1,[],[])` by
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
	      FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,transFrmState,
					transToState,transSym] THEN
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
		     (transFrmState h1,h2 ++ FLAT (MAP SND t),
		      [transSym h1] ++ MAP transSym (MAP FST t))
		     (transToState i1,[],[])` 
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
		  FULL_SIMP_TAC (srw_ss()) [transToState] THEN
		  Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [transFrmState,
					    transToState] THEN1
		  METIS_TAC [RTC_RULES] THEN
		  `LAST t = (NTS (q',q''',r'''),r)` 
		  by METIS_TAC [last_append,APPEND,APPEND_ASSOC,MEM] THEN
		  
		  `transToState (LAST (q''::MAP FST t))= r'''` 
		  by (`MAP FST t = MAP FST (FRONT t) ++ 
		      MAP FST [(NTS (q',q''',r'''),r)]`
		      by METIS_TAC [MAP_APPEND,APPEND_FRONT_LAST] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      METIS_TAC [transToState,last_append,APPEND,
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
	    `m ⊢ (q,x,[A]) → (q',x,transSym h''::MAP transSym t)` 
	    by SRW_TAC [][id_thm] THEN
	    `∃l0.
	    (h''::t = MAP FST l0) ∧ (x = FLAT (MAP SND l0)) ∧
	    ∀a b.MEM (a,b) l0 ⇒
	    ∃dl0.LENGTH dl0 ≤ LENGTH l ∧ 
	    derives g ⊢ dl0 ◁ [a] → b` by 
	    METIS_TAC [listPairExistsLd] THEN
	    SRW_TAC [][] THEN

	    `∀e1 e2.MEM (e1,e2) l0 ⇒ 
	    (ID m)^* (transFrmState e1,e2,[transSym e1]) 
	             (transToState e1,[],[])` by
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
	      FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,transFrmState,
					transToState,transSym] THEN
	      METIS_TAC [everyFlat]) THEN
	     `t''=[]` by (Cases_on `t''` THEN 
			FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq]) THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `EVERY isNonTmnlSym (MAP FST r1''' ++ [TS t'''] ++ MAP FST r2''')`
	     by METIS_TAC [EVERY_DEF,EVERY_APPEND] THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]) THEN
	     
	    FULL_SIMP_TAC (srw_ss()) [ntslCond] THEN
	    `∀i2 i1.(LAST l0 = (i1,i2)) ⇒
		     ∀t h2 h1.(l0 = (h1,h2)::t) ⇒
		     (ID m)^*
		     (transFrmState h1,h2 ++ FLAT (MAP SND t),
		      [transSym h1] ++ MAP transSym (MAP FST t))
		     (transToState i1,[],[])` 
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
		  FULL_SIMP_TAC (srw_ss()) [transToState] THEN
		  Cases_on `t''=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  FULL_SIMP_TAC (srw_ss()) [transFrmState,
					    transToState] THEN
		  `LAST t'' = (NTS (q',q'',r'''),r)` 
		  by METIS_TAC [last_append,APPEND,APPEND_ASSOC,MEM] THEN
		  
		  `transToState (LAST (h''::MAP FST t''))= r'''` 
		  by (`MAP FST t'' = MAP FST (FRONT t'') ++ 
		      MAP FST [(NTS (q',q'',r'''),r)]`
		      by METIS_TAC [MAP_APPEND,APPEND_FRONT_LAST] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      METIS_TAC [transToState,last_append,APPEND,
				 last_elem]) THEN
		  METIS_TAC [RTC_RULES],

		  FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
		  `EVERY isNonTmnlSym (MAP FST (FRONT t''++[(TS t,r)]))`
		  by METIS_TAC [APPEND_FRONT_LAST,last_append,APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]
		  ]]]);


val _ = export_theory ();