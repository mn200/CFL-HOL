open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory containerTheory pairTheory boolSimps
optionTheory rich_listTheory

open symbolDefTheory parseTreeTheory grammarDefTheory listLemmasTheory
firstSetDefTheory followSetDefTheory containerLemmasTheory
setLemmasTheory boolLemmasTheory whileLemmasTheory relationLemmasTheory

val _ = new_theory "yaccDef"
fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val _ = Globals.linewidth := 60
val _ = diminish_srw_ss ["list EQ"];

val _ = Hol_datatype 
`item = item of 'nts => ('nts,'ts) symbol list # ('nts,'ts) symbol list`; 

val _ = type_abbrev ("state", ``:('nts,'ts) item list``);

val _ = Hol_datatype `action = 
    REDUCE of ('nts,'ts) rule | GOTO of ('nts,'ts) state | NA`;


val getItems = Define `
(getItems [] s = []) ∧ 
(getItems ((rule l r)::rs) s = if (l=s) then (item l ([],r)::getItems rs s) 
			       else getItems rs s)`;

(* iclosure :: grammar -> item list -> item list *)
val iclosure1 = Define 
`(iclosure1 g [] = []) ∧
(iclosure1 g ((item s (l1,[]))::il) = ((item s (l1,[]))::iclosure1 g il)) ∧
(iclosure1 g ((item s (l1,TS ts::l2))::il) = 
 (((item s (l1,TS ts::l2)))::iclosure1 g il)) ∧
(iclosure1 g ((item s (l1,NTS nt::l2))::il) = 
(getItems (rules g) nt ++ [(item s (l1,NTS nt::l2))] ++ iclosure1 g il))`;


(* iclosure :: grammar -> item list -> item list *)
val iclosure1 = Define `(iclosure1 g [] = []) ∧
(iclosure1 g ((item s (l1,[]))::il) = ((item s (l1,[]))::iclosure1 g il)) ∧
(iclosure1 g ((item s (l1,TS ts::l2))::il) = 
 (((item s (l1,TS ts::l2)))::iclosure1 g il)) ∧
(iclosure1 g ((item s (l1,NTS nt::l2))::il) = 
(getItems (rules g) nt ++ [(item s (l1,NTS nt::l2))] ++ iclosure1 g il))`;


val iclosure_defn = Hol_defn 
"iclosure_defn" 
`(iclosure g [] = []) ∧
(iclosure g il = 
	let
	    ril = rmDupes il
	    in
		let
		    al = rmDupes (iclosure1 g ril)
		in 
		    if ~(LIST_TO_SET ril = LIST_TO_SET al) then iclosure g al
		    else al)`;


val closure = Define
`closure g itl = 
      { item sym ([],r) | 
       ∃l r1 r2 nt sfx. MEM (item l (r1,NTS nt::r2)) itl ∧
       RTC (derives g) [NTS nt] (NTS sym::sfx) ∧
       MEM (rule sym r) (rules g) }`;


val rules2Items = Define 
`(rules2Items [] = []) ∧
(rules2Items (rule l r::rst) = item l ([], r)::rules2Items rst)`;

val iclosure1_mem = store_thm ("iclosure1_mem", 
``∀e l.MEM e l ⇒ (MEM e (iclosure1 g l))``,
Induct_on `l` THEN SRW_TAC [] [] THENL[
Cases_on `e`  THEN Cases_on `p` THEN Cases_on `r` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_1, MEM],
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_1, MEM, APPEND, CONS, rgr_r9eq, MEM_APPEND]],
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_1, MEM, APPEND, CONS, rgr_r9eq, MEM_APPEND]]);



val iclosure1_not_nil = store_thm ("iclosure1_not_nil", 
``∀g x xs.~(iclosure1 g (x::xs) = [])``,
Cases_on `x` THEN Cases_on `p` THEN Cases_on `r` THENL[
SRW_TAC [] [iclosure1, rmDupes_not_nil],
Cases_on `h` THEN SRW_TAC [] [iclosure1, rmDupes_not_nil] THEN
Cases_on `getItems (rules g) s'` THEN SRW_TAC [] [iclosure1, rmDupes_not_nil]]);

val iclosure1_len = store_thm ("iclosure1_len", 
``∀g l.LENGTH (iclosure1 g l) >= LENGTH (rmDupes l)``,
Induct_on `iclosure1 g l` THEN SRW_TAC [] [] THEN
Induct_on `l` THEN SRW_TAC [] [iclosure1, rmDupes] THENL[
METIS_TAC [iclosure1_not_nil],
`~(iclosure1 g (h'::l) = [])` by METIS_TAC [iclosure1_not_nil] THEN
`∀e.MEM e (h'::l) ⇒ MEM e (iclosure1 g (h'::l))` by METIS_TAC [iclosure1_mem] THEN
`LENGTH (h'::l) >= SUC (LENGTH l)` by FULL_SIMP_TAC (arith_ss) [LENGTH] THEN
`LENGTH (iclosure1 g (h'::l)) >= LENGTH (rmDupes (h'::l))` 
by METIS_TAC [mem_subset_len, rmd_r2] THEN
FULL_SIMP_TAC (arith_ss) [rmDupes, MEM, APPEND, LENGTH]]);

val rmd_del_eq_list = 
store_thm ("rmd_del_eq_list",
 ``∀e l.(rmDupes (delete e l) = l) ⇒
      (rmDupes l = l)``,
Induct_on `l` THEN SRW_TAC [] [rmDupes,delete_def] 
THENL[
      METIS_TAC [not_mem_delete,MEM,rmd_mem_list],

      Cases_on `MEM h l`
      THENL[
	    METIS_TAC [not_mem_delete,MEM,rmd_mem_list],

	    Cases_on `MEM e l` THEN
	    METIS_TAC [delete_not_mem,MEM,rmd_mem_list,not_mem_delete,
		       delete_mem_list]
	    ]
      ]);

val rules2items_sub = store_thm ("rules2items_sub",
``∀e lhs rs.MEM e (getItems rs lhs) ⇒ MEM e (rules2Items rs)``,
Induct_on `rs` THEN SRW_TAC [] [getItems, rules2Items] THEN
Cases_on `h` THEN  FULL_SIMP_TAC (srw_ss()) [rules2Items, getItems] THEN
Cases_on `s=lhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [MEM, rules2Items, getItems, APPEND]);

val iclosure1_outmem = store_thm ("iclosure1_outmem", 
``∀e l.MEM e (iclosure1 g l) ⇒ ~(MEM e l) ⇒ (MEM e (rules2Items (rules g)))``,
Induct_on `l` THEN SRW_TAC [] [iclosure1] THEN
Cases_on `h` THEN  Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_2, MEM, MEM_APPEND, rules2items_sub]);


val iclosure1_before_after_len = store_thm ("iclosure1_before_after_len",
``∀l.(CARD (set (iclosure1 g l)) > CARD (set l)) ⇒ 
((CARD (set (rules2Items (rules g)) INTER set (iclosure1 g l)) -
CARD (set (rules2Items (rules g)) INTER (set l))) > 0)``,
SRW_TAC [] [] THEN
`(set l) SUBSET (set (iclosure1 g l))` by METIS_TAC [mem_subset, iclosure1_mem] THEN
`∃e.~(e IN set l) ∧ (e IN set (iclosure1  g l))` by METIS_TAC [set_neq, FINITE_LIST_TO_SET] THEN
`MEM e (iclosure1 g l)` by METIS_TAC [IN_LIST_TO_SET] THEN
`~(MEM e l)` by METIS_TAC [IN_LIST_TO_SET] THEN
`MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem] THEN
`e IN set (rules2Items (rules g))` by METIS_TAC [IN_LIST_TO_SET] THEN
`~(set l= set (iclosure1 g l))` by METIS_TAC [LIST_TO_SET_THM, IN_LIST_TO_SET] THEN
`(set l) PSUBSET set (iclosure1 g l)` by METIS_TAC [PSUBSET_DEF] THEN
`CARD (set l) < CARD (set (iclosure1 g l))` by METIS_TAC [CARD_PSUBSET, 
							  FINITE_LIST_TO_SET] THEN
`CARD (set l) < CARD (set (iclosure1 g l))` by METIS_TAC [CARD_PSUBSET, 
							  FINITE_LIST_TO_SET] THEN
`CARD (set l INTER (set (rules2Items (rules g)))) 
< CARD (set (iclosure1 g l) INTER (set (rules2Items (rules g))))` 
by METIS_TAC [card_same_inter, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (arith_ss) [INTER_COMM]);


val (iclosure, iclosure_ind) = tprove(iclosure_defn,
WF_REL_TAC `measure (\(g,al).CARD (set (rules2Items (rules g)) DIFF (set al)))` THEN
SRW_TAC [] [] THENL[
(*1*)
`∀e.MEM e (rmDupes (v2::v3)) ⇒ MEM e (iclosure1 g (rmDupes (v2::v3)))` by 
METIS_TAC [iclosure1_mem] THEN
`∀e.MEM e (iclosure1 g (rmDupes (v2::v3))) ⇒ 
		    MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
by  METIS_TAC [rmd_r2] THEN
`∀e.MEM e (rmDupes (v2::v3)) ⇒ MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
		    by METIS_TAC []
THEN
`LENGTH (rmDupes (iclosure1 g (rmDupes (v2::v3)))) >= LENGTH (rmDupes (v2::v3))` by
METIS_TAC [mem_subset_len] THEN
`CARD (set (rmDupes (iclosure1 g (rmDupes (v2::v3))))) >= 
		    CARD (set (rmDupes (v2::v3)))`  by 
METIS_TAC [list_set_len, rmDupes_twice] THEN
`∀e.MEM e (rmDupes (v2::v3)) ⇒ MEM e (iclosure1 g (rmDupes (v2::v3)))` by 
METIS_TAC [iclosure1_mem] THEN
`(set (v2::v3)) SUBSET (set (iclosure1 g (rmDupes (v2::v3))))` by  
METIS_TAC [mem_subset, rmDupes_lts] THEN
`CARD (set (iclosure1 g (rmDupes (v2::v3)))) > CARD (v2 INSERT set v3)` by 
METIS_TAC [set_neq_len, iclosure1_mem, FINITE_LIST_TO_SET, mem_subset, LIST_TO_SET_THM, rmDupes_lts] THEN
`∃e.e IN (set (iclosure1 g (rmDupes (v2::v3)))) ∧ ~(e IN (v2 INSERT set v3))` by
METIS_TAC [set_neq, FINITE_LIST_TO_SET, rmDupes_lts, LIST_TO_SET_THM] THEN
`MEM e (iclosure1 g (rmDupes (v2::v3)))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST] THEN
`~(MEM e (v2::v3))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST] THEN
`MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem, rmd_r2] THEN
`e IN (set (rules2Items (rules g)))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(e IN (v2 INSERT set v3))`  by FULL_SIMP_TAC (srw_ss()) [] THEN
`CARD (set (rules2Items (rules g))) - CARD (set (rules2Items (rules g)) INTER (v2 INSERT set v3)) > 0` by METIS_TAC [inter_card_less, FINITE_LIST_TO_SET] THEN
`CARD (set (rules2Items (rules g)) INTER set (rmDupes (iclosure1 g (rmDupes (v2::v3))))) -
CARD (set (rules2Items (rules g)) INTER (v2 INSERT set v3)) > 0` by 
METIS_TAC [iclosure1_before_after_len, LIST_TO_SET_THM, rmDupes_lts] THEN
FULL_SIMP_TAC (arith_ss) [],

(*2*)
`∀e.MEM e (rmDupes (v2::v3)) ⇒ MEM e (iclosure1 g (rmDupes (v2::v3)))` by 
METIS_TAC [iclosure1_mem] THEN
`∀e.MEM e (iclosure1 g (rmDupes (v2::v3))) ⇒ MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
by  METIS_TAC [rmd_r2] THEN
`∀e.MEM e (rmDupes (v2::v3)) ⇒ MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` by METIS_TAC []
THEN
`LENGTH (rmDupes (iclosure1 g (rmDupes (v2::v3)))) >= LENGTH (rmDupes (v2::v3))` by
METIS_TAC [mem_subset_len] THEN
`CARD (set (rmDupes (iclosure1 g (rmDupes (v2::v3))))) >= CARD (set (rmDupes (v2::v3)))`  by 
METIS_TAC [list_set_len, rmDupes_twice] THEN
`∀e.MEM e (rmDupes (v2::v3)) ⇒ MEM e (iclosure1 g (rmDupes (v2::v3)))` 
by METIS_TAC [iclosure1_mem] THEN
`(set (v2::v3)) SUBSET (set (iclosure1 g (rmDupes (v2::v3))))` by  
METIS_TAC [mem_subset, rmDupes_twice, LIST_TO_SET_THM, FINITE_LIST_TO_SET, rmDupes_lts] THEN
`CARD (set (iclosure1 g (rmDupes (v2::v3)))) > CARD (v2 INSERT set v3)` by 
METIS_TAC [set_neq_len, iclosure1_mem, FINITE_LIST_TO_SET, LIST_TO_SET_THM, rmDupes_lts] THEN
`∃e.e IN (set (iclosure1 g (rmDupes (v2::v3)))) ∧ ~(e IN (v2 INSERT set v3))` by
METIS_TAC [set_neq, FINITE_LIST_TO_SET, rmDupes_lts, LIST_TO_SET_THM] THEN
`MEM e (iclosure1 g (rmDupes (v2::v3)))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST] THEN
`~(MEM e (v2::v3))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST, rmd_r2_1] THEN
`MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem, rmd_r2] THEN
`e IN (set (rules2Items (rules g)))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(e IN (v2 INSERT set v3))`  by FULL_SIMP_TAC (srw_ss()) [] THEN
`CARD (set (rules2Items (rules g))) - CARD (set (rules2Items (rules g)) INTER (v2 INSERT set v3)) > 0` by METIS_TAC [inter_card_less, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (arith_ss) []]);


val _ = save_thm ("iclosure",iclosure);
val _ = save_thm ("iclosure_ind",iclosure_ind);

val iclosure_nil = store_thm ("iclosure_nil", 
``∀g l.~(l=[]) ⇒ ~(iclosure g l = [])``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [] THEN
SRW_TAC [] [iclosure, LET_THM] THEN
METIS_TAC [iclosure1_not_nil, rmDupes_not_nil, len_not_0, LENGTH_NIL]);


val auggr = Define `(auggr g s eof = 	
         if ((~((NTS s) IN (nonTerminalsML g)) ∧ 
	    (~ ((TS eof) IN (terminalsML g))))) then 
         SOME (G ([(rule s [NTS (startSym g); TS eof])]++(rules g)) s) 
         else NONE)`;




val lastEof = store_thm ("lastEof",
``∀g st eof.(auggr g st eof = SOME ag) ⇒ 
  ∀l.RTC (rderives ag) [NTS (startSym ag)] (pfx++[NTS N]++sfx) ⇒ ~(N=startSym ag)
  ⇒ ∃pfx'.(sfx = pfx'++[TS eof])``,
SRW_TAC [] [auggr, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1, lreseq, rderives_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
SRW_TAC [] [] THEN
`∃pfx'.(pfx ++ [NTS N] ++ sfx)=pfx'++[TS eof]` by METIS_TAC [rtcRderivesLastTmnl, APPEND] THEN
Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`NTS N = TS eof` by METIS_TAC [last_elem] THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [lastListBdown, NOT_CONS_NIL, last_append, last_elem]],
METIS_TAC [slemma1_4, nonTerminalsEq]]);


val auggr_startSym = store_thm ("auggr_startSym", 
``(auggr g st eof = SOME ag) ⇒ (startSym ag = st)``,
SRW_TAC [] [auggr] THEN SRW_TAC [] [startSym_def]);


val auggr_not_rd_nts = store_thm ("auggr_not_rd_nts",
``∀g st eof N.(auggr g st eof = SOME ag) ⇒ ~(N=st) ⇒ 
~ (RTC (rderives ag) [NTS (startSym ag)] [NTS N])``,
SRW_TAC [] [Once RTC_CASES1] THENL[
METIS_TAC [auggr_startSym],
FULL_SIMP_TAC (srw_ss()) [auggr, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g)` THEN 
Cases_on `~(TS eof IN terminalsML g)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def, startSym_def] THEN
Cases_on `~rderives (G (rule st [NTS (startSym g); TS eof]::rules g) st) [NTS st] u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq, rules_def] THENL[
`MEM (TS eof) [NTS (startSym g); TS eof]` by SRW_TAC [] [] THEN
Cases_on `RTC (rderives (G (rule st [NTS (startSym g); TS eof]::rules g) st))
       [NTS (startSym g); TS eof] [NTS N]` THENL[
`MEM (TS eof) [NTS N]` by METIS_TAC [rtc_rderives_has_tmnl] THEN
FULL_SIMP_TAC (srw_ss()) [],
FULL_SIMP_TAC (srw_ss()) []],
METIS_TAC [slemma1_4, nonTerminalsEq]]]);


val auggr_eq_start_rule = store_thm ("auggr_eq_start_rule",
``∀g st eof N r1 h.(auggr g st eof = SOME ag) ⇒ 
(MEM (rule st (r1 ++ [h])) (rules ag)) ⇒ 
((r1=[NTS (startSym g)]) ∧ (h=TS eof))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [auggr, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g)` THEN 
Cases_on `~(TS eof IN terminalsML g)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
Cases_on `r1` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
Cases_on `t` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def],
METIS_TAC [slemma1_4, nonTerminalsEq],
Cases_on `r1` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
Cases_on `t` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def],
METIS_TAC [slemma1_4, nonTerminalsEq]]);



val auggrStartRule = store_thm ("auggrStartRule", 
``∀g st eof h.(auggr g st eof = SOME ag) 
  ⇒ MEM (rule (startSym ag) h) (rules ag)
  ⇒ (h=[NTS (startSym g);TS eof])``,
SRW_TAC [] [auggr, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
METIS_TAC [slemma1_4, nonTerminalsEq]);


val auggrNotStInRtcRderives = store_thm ("auggrNotStInRtcRderives",
``∀u v.RTC (rderives ag) u v ⇒ (u=[NTS (startSym g); TS eof]) ⇒ 
(auggr g st eof = SOME ag) ⇒ ~(MEM (NTS (startSym ag)) v)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [auggr, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g) ∧ ~(TS eof IN terminalsML g)` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [nonTerminalsEq, slemma1_4, startSym_def],
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
METIS_TAC [slemma1_4, nonTerminalsEq, startSym_def, rgr_r9eq]]);


val auggrStRtcDerivesSt = store_thm ("auggrStRtcDerivesSt",
``∀u v.RTC (rderives ag) u v ⇒ (u=[NTS (startSym ag)]) ⇒ 
  (auggr g st eof = SOME ag) ⇒ ((v=[NTS (startSym ag)]) ∨ ~(MEM (NTS (startSym ag)) v))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
`u'=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [auggrNotStInRtcRderives]);


val auggrRtcRderivesPfxSfxNil = store_thm ("auggrRtcRderivesPfxSfxNil",
``∀e pfx sfx.(auggr g st eof = SOME ag) ⇒
RTC (rderives ag) [NTS (startSym ag)] (pfx++[NTS (startSym ag)]++sfx) ⇒ 
(pfx=[]) ∧ (sfx=[])``,
SRW_TAC [] [] THEN
`(pfx ++ [NTS (startSym ag)] ++ sfx = [NTS (startSym ag)]) ∨ 
~(MEM (NTS (startSym ag)) (pfx ++ [NTS (startSym ag)] ++ sfx))` by METIS_TAC [auggrStRtcDerivesSt] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq]);

val auggrRtcRderivesStartRule = store_thm ("auggrRtcRderivesStartRule",
``∀u v.RTC (rderives ag) u v ⇒ (u=[NTS (startSym ag)])  ⇒ 
      (auggr g st eof = SOME ag) ⇒  
     ~(v=[NTS (startSym ag)]) ⇒ RTC (rderives ag)  [NTS (startSym g); TS eof] v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∀h.MEM (rule (startSym ag) h) (rules ag) ⇒
         (h = [NTS (startSym g); TS eof])` by METIS_TAC [auggrStartRule] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []);

val auggrDerivesNotNil = store_thm ("auggrDerivesNotNil",
``∀g st eof.
            (auggr g st eof = SOME ag) ⇒
            ∀l.
              RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ⇒
              ~(N = startSym ag) ⇒ ~(sfx=[])``,
SRW_TAC [] [] THEN
`∃pfx'. sfx = pfx' ++ [TS eof]` by METIS_TAC [lastEof] THEN
FULL_SIMP_TAC (srw_ss()) []);


val auggrStRtcRderivesNotNil = store_thm ("auggrStRtcRderivesNotNil",
``(auggr g st eof = SOME ag) ⇒ ~RTC (rderives ag) [NTS (startSym ag)] []``,
SRW_TAC [] [Once RTC_CASES1] THEN
Cases_on `~rderives ag [NTS (startSym ag)] u` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
`u=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`MEM (TS eof)  [NTS (startSym g); TS eof]` by SRW_TAC [] [] THEN
Cases_on `RTC (rderives ag) [NTS (startSym g); TS eof] []` THEN SRW_TAC [] [] THEN
METIS_TAC [rgr_r9eq, MEM, MEM_APPEND, APPEND, rtc_rderives_has_tmnl]);

val auggrRtcRderivesSt = store_thm ("auggrRtcRderivesSt",
``(auggr g st eof = SOME ag) ⇒ RTC (rderives ag) [NTS (startSym ag)] [NTS lhs] ⇒ (lhs=startSym ag)``,
SRW_TAC [] [Once RTC_CASES1] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
`u=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`MEM (TS eof)  [NTS (startSym g); TS eof]` by SRW_TAC [] [] THEN
`MEM (TS eof) [NTS lhs]` by METIS_TAC [rgr_r9eq, MEM, MEM_APPEND, APPEND, rtc_rderives_has_tmnl] THEN
FULL_SIMP_TAC (srw_ss()) []);


val auggrStNotInRhs = store_thm ("auggrStNotInRhs",
``(auggr g st eof = SOME ag) ⇒
  ~(∃lhs rhs p s.MEM (rule lhs (p++[NTS (startSym ag)]++s)) 
   (rules ag))``,
SRW_TAC [] [auggr, LET_THM, startSym_def, rules_def] THEN
`~(∃rhs.
    MEM (rule st rhs) (rules g) ∨
   ∃l p s.
    MEM (rule l (p ++ [NTS st] ++ s)) (rules g) ∨ 
   (st = startSym g))` by METIS_TAC [slemma1_4, nonTerminalsEq] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
Cases_on `~(lhs = st) ∨ ~(p ++ [NTS st] ++ s = [NTS (startSym g); TS eof])` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `p` THEN Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) []
THENL[
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [],
      FULL_SIMP_TAC (srw_ss()) [lreseq]    
      ]);



val auggrNNeqSt = store_thm ("auggrNNeqSt",
``∀pfx sfx.RTC (rderives ag) [NTS (startSym ag)] 
                             (pfx ++ [NTS N] ++ sfx) ⇒
  (auggr g st eof = SOME ag) ⇒
  (~(pfx=[]) ∨ ~(sfx=[])) ⇒
  ~(N=startSym ag)``,
SRW_TAC [] [] THEN
Cases_on `N=startSym ag` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [auggrStNotInRhs, rtcRderivesInRuleRhs]);



val auggrStRtcRderivesSing = store_thm ("auggrStRtcRderivesSing", 
``(auggr g st eof = SOME ag) ⇒  (isTmnlSym h) ⇒ 
RTC (rderives ag) [NTS (startSym ag)] [h] ⇒ (h=TS eof)``,
SRW_TAC [] [Once RTC_CASES2] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN Cases_on `rhs` THEN Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] 
THENL[
 Cases_on `lhs=startSym ag` 
 THENL[
 METIS_TAC [auggrStartRule, NOT_CONS_NIL],

 `∃pfx'.[TS s] = pfx'++[TS eof]` by METIS_TAC [lastEof, APPEND] THEN
 `TS s = TS eof` by METIS_TAC [lastElemEq, APPEND_NIL] THEN
 FULL_SIMP_TAC (srw_ss()) []
 ],

 Cases_on `lhs=startSym ag` 
 THENL[
       SRW_TAC [] [] THEN
       `[TS s] = [NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
       FULL_SIMP_TAC (srw_ss()) [],

       `∃pfx'.[] = pfx'++[TS eof]` by METIS_TAC [APPEND, NOT_CONS_NIL, lastEof, APPEND_NIL] THEN
       Cases_on `pfx'` THEN FULL_SIMP_TAC (srw_ss()) []     
       ],

 Cases_on `lhs=startSym ag` 
 THENL[
 METIS_TAC [auggrStartRule, NOT_CONS_NIL],

 `∃pfx'.[TS s] = pfx'++[TS eof]` by METIS_TAC [lastEof, APPEND] THEN
 `TS s = TS eof` by METIS_TAC [lastElemEq, APPEND_NIL] THEN
 FULL_SIMP_TAC (srw_ss()) []
 ]]);
 
val auggrAllTmsRhs = store_thm ("auggrAllTmsRhs",
``(auggr g st eof = SOME ag) ⇒
   MEM (rule N rhs) (rules ag) ⇒
   EVERY isTmnlSym rhs ⇒
   ~(MEM (TS eof) rhs)``,			
SRW_TAC [] [auggr, LET_THM, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def]
THENL[

      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      Cases_on `~MEM (TS eof) rhs` THEN
      FULL_SIMP_TAC (srw_ss()) []  THEN
      `~(∃l p s. MEM (rule l (p ++ [TS eof] ++ s)) (rules g))` 
       by METIS_TAC [terminalsEq, slemma1_4Tmnls] THEN
      METIS_TAC [rgr_r9eq]
      ]);


val auggrEofInRhs = store_thm ("auggrEofInRhs",
``(auggr g st eof = SOME ag) ⇒
  (MEM (rule lhs rhs) (rules ag)) ⇒
  MEM (TS eof) rhs ⇒
  (lhs = startSym ag)``,
SRW_TAC [] [auggr, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def]THEN
METIS_TAC [rgr_r9eq, slemma1_4Tmnls, terminalsEq]);



val auggrRtcRdLastSymEof = store_thm ("auggrRtcRdLastSymEof",
``∀u v.RTC (rderives ag) u v ⇒ (u=[NTS (startSym ag)]) ⇒
(auggr g st eof = SOME ag) ⇒
MEM (TS eof) v ⇒ 
(LAST v = TS eof)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_APPEND]
THENL[
      `(LAST (s1 ++ [NTS lhs] ++ s2) = TS eof)` by METIS_TAC [] THEN
      Cases_on `s2` THEN
      FULL_SIMP_TAC (srw_ss()) [],

      `lhs=startSym ag` by METIS_TAC [auggrEofInRhs] THEN
      SRW_TAC [] [] THEN
      `(s1=[]) ∧ (s2=[])`by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `rhs=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
      METIS_TAC [APPEND, last_elem],

      Cases_on `s2` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [last_append, NOT_CONS_NIL]
      ]);




val auggrNewRuleMem = 
store_thm ("auggrNewRuleMem",
``(auggr g st eof = SOME ag) ⇒
MEM (rule (startSym ag) [NTS (startSym g);TS eof]) (rules ag)``,
SRW_TAC [][auggr,LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def,rules_def]);

val auggrStNeqOSt =store_thm
("auggrStNeqOSt",
``(auggr g st eof = SOME ag) ⇒
  ~(startSym g = startSym ag)``,
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def,auggr,LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g) ∧
             ~(TS eof IN terminalsML g)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][rules_def,startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) []  THEN
Cases_on `~(startSym g = st)` THEN
SRW_TAC [][] THEN
METIS_TAC [slemma1_4,nonTerminalsEq]
);

val auggr_neqStartSym2 = store_thm ("auggr_neqStartSym2", 
``(auggr g st eof = SOME ag) ⇒ 
MEM (rule n l) (rules ag) ⇒ ~(LAST l = TS eof) ⇒ ~(n=st)``,
SRW_TAC [] [auggr] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
METIS_TAC [last_elem, APPEND],
Cases_on `n=st` THEN
METIS_TAC [slemma1_4, nonTerminalsEq]]);


val lang2rtc2list = store_thm ("lang2rtc2list",
``(auggr g st eof = SOME ag) ⇒
  sl IN language ag ⇒
  ((rderives ag [NTS (startSym ag)] [NTS (startSym g);TS eof]) 
∧ ∃dtl.
   rtc2list (rderives ag) (([NTS (startSym g);TS eof]) :: dtl)
∧ ((LAST (([NTS (startSym g);TS eof])::dtl)) = sl) 
∧ MEM (rule (startSym ag) ([NTS (startSym g);TS eof])) (rules ag))``,

SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [rderives_def,auggr,LET_THM] THEN
      Cases_on `~(NTS st IN nonTerminalsML g) 
		∧~(TS eof IN terminalsML g)` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][rules_def,startSym_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [APPEND_NIL,auggr_startSym,EVERY_DEF],

      `∃dl.rtc2list (rderives ag) dl ∧
       (HD dl = [NTS (startSym ag)]) ∧ (LAST dl = sl)` 
	  by METIS_TAC [rtc2list_exists,listderiv_def] THEN
      SRW_TAC [][] THEN
      Cases_on `dl` THEN
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
      Cases_on `t` THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,language_def,EXTENSION] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def,rderives_def,lreseq] THEN
      SRW_TAC [][] THEN
      `h'=[NTS (startSym g);TS eof]`by METIS_TAC [auggrStartRule] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.EXISTS_TAC `t'`THEN
      SRW_TAC [][]
      ]);

val ag_new_rule = store_thm("ag_new_rule", 
``∀g s eof.(auggr g s eof = SOME ag)
⇒ (MEM (rule s [NTS (startSym g);TS eof]) (rules ag) ∧ (s=startSym ag))``,
SRW_TAC [] [auggr, rules_def, MEM, startSym_def, APPEND, MEM_APPEND] THEN
SRW_TAC [] [auggr, rules_def, MEM, startSym_def, APPEND, MEM_APPEND]);


val initProds2Items = Define 
`(initProds2Items s [] = []) ∧
(initProds2Items s ((rule l r)::rs) = 
 if (s=l) then (((item l ([],r)))::initProds2Items s rs) else initProds2Items s rs)`;


val auggrExistsMemInit = store_thm ("auggrExistsMemInit",
``(auggr g s eof = SOME ag) ⇒ 
      MEM (item (startSym ag) ([],[NTS (startSym g);TS eof])) (initProds2Items (startSym ag) (rules ag))``,
SRW_TAC [] [auggr, LET_THM, startSym_def, rules_def, initProds2Items] THEN
SRW_TAC [] [startSym_def, rules_def, initProds2Items]);


val initItems = Define
(`(initItems g r = iclosure g (initProds2Items (startSym g) r))`);
(*
Induct_on `r` THEN SRW_TAC [] [initItems, initProds2Items, iclosure] THEN
Cases_on `h` THEN SRW_TAC [] [initItems, initProds2Items, iclosure] THEN

*)


(* Given an itemset and a symbol, move the dot to the right of the symbol *)
(*val moveDot = Define `moveDot its sym = {item s (pfx++[sym],sfx) | item s (pfx,[sym]++sfx) IN its}`*)




 val moveDot = Define `(moveDot [] sym = []) ∧
 (moveDot ((item str (a,(s::ss)))::it) sym =  
if (s=sym) then (item str (a++[s],ss))::moveDot it sym else moveDot it sym) ∧
 (moveDot (_::it) sym = moveDot it sym)`;

val trans = Define
`(trans ag (s,[]) = SOME s) ∧
 (trans ag (s,sym::rst) =
    case moveDot s sym of 
       [] -> NONE
    || x -> trans ag (iclosure ag x, rst))`;
 

val EXISTS_item = store_thm("EXISTS_item",
  ``(∃i:('nts,'ts) item. P i) = ∃N p s. P (item N (p,s))``,
  SRW_TAC [][EQ_IMP_THM] THENL[
    Cases_on `i` THEN Cases_on `p` THEN METIS_TAC [],
    METIS_TAC []
  ]);

(* nextState :: grammar -> item list -> symbol -> item list option *)

val nextState = Define `nextState g itl sym = iclosure g (moveDot itl sym)`

val validItl = Define 
`(validItl g [] = T) ∧
(validItl g (item l (r1,r2) :: rst) = 
MEM (rule l (r1++r2)) (rules g) ∧ validItl g rst)`;

val validStates = Define `(validStates g [] = T) ∧
(validStates g ((sym, itl)::rst) = validItl g itl ∧ validStates g rst)`;

val validItl_append = store_thm ("validItl_append",
``validItl g (l1++l2) = validItl g l1 ∧ validItl g l2``,
SRW_TAC [] [EQ_IMP_THM] THENL [
Induct_on `l1` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [validItl] THEN 
Cases_on `h` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [validItl],
Induct_on `l2` THEN SRW_TAC [] [] THEN Induct_on `l1` THEN 
FULL_SIMP_TAC (srw_ss()) [validItl] THEN 
SRW_TAC [] [] THEN Cases_on `h'` THEN Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [validItl],
Induct_on `l2` THEN SRW_TAC [] [] THEN Induct_on `l1` THEN 
FULL_SIMP_TAC (srw_ss()) [validItl] THEN 
SRW_TAC [] [] THEN Cases_on `h'` THEN 
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [validItl]]
);


val validStates_append = store_thm ("validStates_append", 
``∀l1 l2.validStates g (l1 ++ l2) = validStates g l1 ∧ validStates g l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [validStates] THEN
Cases_on `h'` THEN METIS_TAC [validStates, APPEND]);


val validStates_pop = store_thm ("validStates_pop", 
``∀g l n.validStates g l ⇒ validStates g (pop l n)``,
METIS_TAC [popl, validStates_append]);

val validItl_md = store_thm ("validItl_md",
``∀itl sym.validItl g itl ⇒ validItl g (moveDot itl sym)``,
Induct_on `itl` THEN SRW_TAC [] [validItl, moveDot] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [validItl, moveDot] THEN
Cases_on `h=sym` THEN SRW_TAC [] [validItl] THEN 
METIS_TAC [APPEND, APPEND_ASSOC]);


val validItl_rules_cons = store_thm ("validItl_rules_cons",
``∀r s l e.validItl (G r s) l ⇒ validItl (G (e::r) s) l``,
SRW_TAC [] [] THEN
Induct_on `l` THEN SRW_TAC [] [validItl] THEN
Cases_on `h` THEN Cases_on `p`  THEN FULL_SIMP_TAC (srw_ss()) [validItl, rules_def]);


val rules2items_sub2 = store_thm ("rules2items_sub2",
``∀g.validItl g  (rules2Items (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [validItl, rules2Items] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validItl, rules_def, rules2Items] THEN
METIS_TAC [validItl_rules_cons]);


val validItl_mem = store_thm ("validItl_mem",
``∀l.validItl g l = (∀e.MEM e l ⇒ validItl g [e])``,
Induct_on `l` THEN SRW_TAC [] [validItl, EQ_IMP_THM] THEN
METIS_TAC [validItl_append, APPEND]);



val validItl_getItems = store_thm ("validItl_getItems",
``∀sym.validItl g (getItems (rules g) sym)``,

Induct_on `rules g` THEN SRW_TAC [] [validItl, getItems] THEN1
METIS_TAC [validItl, getItems] THEN
`rules g = h::v` by METIS_TAC [] THEN 
Cases_on `h` THEN ONCE_ASM_REWRITE_TAC [] THEN
`∀e.MEM e (getItems (rule n l::v) sym) ⇒ MEM e (rules2Items (rule n l::v))` 
				   by METIS_TAC [rules2items_sub] THEN
`validItl g (rules2Items (rule n l ::v))` 
by METIS_TAC [rules2items_sub2, rules_def,validItl] THEN
`∀e.MEM e (rules2Items (rule n l::v)) ⇒ validItl g [e]` 
				   by METIS_TAC [validItl_mem] THEN
METIS_TAC [validItl_mem, APPEND, validItl_append]);


val validItl_iclosure1 = store_thm ("validItl_iclosure1", 
``∀g itl.validItl g itl ⇒ validItl g (iclosure1 g itl)``,
Induct_on `itl` THEN SRW_TAC [] [validItl, iclosure1] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1, validItl] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1, validItl] THEN
METIS_TAC [validItl, validItl_append, APPEND, APPEND_ASSOC, validItl_getItems]);


val validItl_delete = store_thm ("validItl_delete",
``∀g t h.validItl g t ⇒ validItl g (delete h t)``,
Induct_on `t` THEN SRW_TAC [] [delete_def, validItl] THEN
METIS_TAC [validItl_append, APPEND]);


val validItl_rmDupes = store_thm ("validItl_rmDupes", 
``∀itl.validItl g itl ⇒ validItl g (rmDupes itl)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, validItl] THEN
METIS_TAC [validItl_append, APPEND, validItl_delete]);


val validItl_iclosure = store_thm ("validItl_iclosure",
``∀g itl.validItl g itl ⇒ validItl g (iclosure g itl)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, validItl, LET_THM] THEN
METIS_TAC [validItl_rmDupes, validItl_iclosure1]);

val sgoto = Define `sgoto g itl sym = nextState g itl sym`;


val validItl_sgoto = store_thm ("validItl_sgoto", 
``∀g itl sym.validItl g itl ⇒ validItl g (sgoto g itl sym)``,
SRW_TAC [] [sgoto, nextState] THEN
`validItl g (moveDot itl sym)` by METIS_TAC [validItl_md] THEN
METIS_TAC [validItl_iclosure]);


(*!!!!Make followSet followSetML*)
val reduce = Define `
(reduce (g:(α,β) grammar) ([]:(α,β) item list) (s:β) = []:(α,β) rule list) ∧ 
(reduce (g:(α,β) grammar) 
(item (l:α) (r:(α,β) symbol list, []:(α,β) symbol list)::it) (s:β)  = 
if ((TS s) IN (followSet g (NTS l))) then 
    ((rule l r)::reduce g it s) else reduce g it s) ∧
(reduce g ((item l (r, _))::it) s = reduce g it s)`;


val buildTree = Define `(buildTree p r = 
			 let s = take (LENGTH r) ((MAP (ptree2Sym o SND) p))
			 in
			     if (s=NONE) then NONE
				 else
				     if (r=THE s) then take (LENGTH r) (MAP SND p)
					 else NONE)`;



val addRule = Define `(addRule p (rule l r) = 
         let x =  buildTree p (REVERSE r) in 
              if (x = NONE) then NONE 
	      else SOME  (Node l (REVERSE (THE x))))`;

(* stack top is the first element *)
(* ptree is a stack of parsetrees *)

(*
Parsing procedure
If terminal symbol -> shift goto or reduce -> both then conflict
nonterminal symbol -> goto or reduce -> both then conflict
accept when all symbols read and only one parse tree exists
*)

val machine = Define `machine g = (sgoto g, reduce g)`;

(* slr :: grammar -> machine option *)
(* 
if reduce returns more than 1 rule -> NONE
if reduce and goto are null -> NONE
if both are not null and return different states -> NONE
----------------
if ∃itl1 itl2, sym IN grammar : sgoto g itl1 sym [] = itl2 ∧ 
iclosure (reduce)
*)



val slrmac = Define `slrmac g =
let
sg = sgoto g and
red = reduce g
in
if (∃pfx itl sym. isTmnlSym sym ∧ (trans g (initItems g (rules g),pfx) = SOME itl) ∧
let
    (s = sg itl sym) and
    (r = red itl (ts2str sym))
in
case (s,r) of (* ([],[]) dealt in the parser *)
 ((x::xs),(y::ys)) -> T
|| (_,(y::y'::ys)) -> T
|| otherwise -> F)
then NONE else SOME (sg,red)`;

val noError = Define
    `(noError (sf,red) [] st = T) ∧
    (noError (sf,red) (sym::rst) st = 
     (st=[]) ∨
     case red st (ts2str sym) of
         []  -> noError (sf,red) rst (sf st sym)
       || [r] -> (sf st sym = [])
       || otherwise -> F)`;

val okSlr = Define
    `okSlr g initState = 
      ∀vp state symlist.
      ((EVERY isTmnlSym symlist ∧ (trans g (initState,vp) = SOME state))
          ⇒
       noError (sgoto g, reduce g) symlist state)`;

val slrmach = Define
    `slrmach g initState = 
      if (okSlr g initState) then SOME (sgoto g, reduce g) else NONE`;

val sgotoItlNil = store_thm
("sgotoItlNil",
``sgoto g [] sym = []``,

SRW_TAC [][sgoto, nextState, moveDot, iclosure]);


(*
val slrmacEqAlt = store_thm 
("slrmacEqAlt",
 ``slrmac g = slrmach g (initItems g (rules g))``,

 SRW_TAC[][slrmac, slrmach] THEN
 FULL_SIMP_TAC (srw_ss()) [Abbrev_def, okSlr] THEN
 SRW_TAC [][] THEN
 Cases_on `sgoto g itl sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (Cases_on `reduce g itl (ts2str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`, `itl`, `[sym]`] MP_TAC) THEN 
  SRW_TAC [][noError] THEN
  Cases_on `itl` THEN FULL_SIMP_TAC (srw_ss()) [reduce]) THEN
 Cases_on `reduce g itl (ts2str sym)` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`, `itl`, `[sym]`] MP_TAC) THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [noError] THEN
 Cases_on `reduce g itl (ts2str sym)` THEN
 Cases_on `sgoto g itl sym` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [trans] THEN
METIS_TAC [sgotoItlNil, NOT_CONS_NIL]

*)




(*
1. get init closure
2. get all symbols in the grammar
3. build the graph

#of symbols after the dot decreases in the common rules between the
 old and the new state
*)

val ruleItems_defn = Hol_defn "ruleItems_defn" 
`(ruleItems (item l (r,[])) = [item l (r,[])]) ∧
(ruleItems (item l ([],x::xs)) = item l ([],x::xs) :: ruleItems (item l ([x],xs))) ∧
(ruleItems (item l (r1,x::xs))  = 
 item l (r1,x::xs) :: ruleItems (item l (r1++[x],xs)))`;

val itemPair = Define `itemPair (item l x) = x`;


val (ruleItems, ruleItems_ind) = tprove (ruleItems_defn,
WF_REL_TAC `measure (\x.(LENGTH (SND (itemPair x))))` THEN 
SRW_TAC [] [itemPair, SND]);

val allItems = Define `(allItems [] = []) ∧
(allItems (rule l r::rs) = ruleItems (item l ([], r)) ++ allItems rs)`;

val symNeighbour = Define 
`(symNeighbour g itl sym = rmDupes (iclosure g (moveDot itl sym)))`;

val asNeighbours = Define `(asNeighbours g itl [] = []) ∧
(asNeighbours g itl (x::xs) =  (symNeighbour g itl x::asNeighbours g itl xs))`;


val visit_defn = Hol_defn "visit_defn" 
`(visit g sn itl = 
if ~(ALL_DISTINCT itl) ∨ ~(validItl g itl) then [] else
let 
s = asNeighbours g itl (SET_TO_LIST (allSyms g)) 
in
		     let
			 rem = diff s sn
		     in
			 rem++(FLAT (MAP (visit g (sn++rem)) rem)))`;

val itemEqRule = Define 
`itemEqRule g (item l (r1,r2)) = MEM (rule l (r1++r2)) (rules g)`;

val isGrammarItl = Define `(isGrammarItl g itl = EVERY (itemEqRule g) itl)`;

val allGrammarItls = Define 
`allGrammarItls g = {itl | isGrammarItl g itl ∧ ALL_DISTINCT itl}`;

val finite_allItems = store_thm ("finite_allItems",
``∀g.FINITE {i|MEM i (allItems (rules g))}``,
`∀g.{i|MEM i (allItems (rules g))} = 
{i|i IN LIST_TO_SET (allItems (rules g))}` by METIS_TAC [setc_mem_in] THEN
SRW_TAC [] [EXTENSION]);

val itemEqRuleRulesEqGrRules = store_thm ("itemEqRuleRulesEqGrRules",
``∀g.{rule l (r1++r2) | itemEqRule g (item l (r1,r2))} = (LIST_TO_SET (rules g))``,
SRW_TAC [] [itemEqRule, SUBSET_DEF, EQ_IMP_THM, EXTENSION] THENL[
METIS_TAC [],
Cases_on `x` THEN Induct_on `l` THEN SRW_TAC [] [] THEN
 METIS_TAC [APPEND]]);

val allItems_append = store_thm ("allItems_append",
``∀l1 l2.allItems (l1++l2) = allItems l1 ++ allItems l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [allItems] THEN
Cases_on `h` THEN Cases_on `h'` THEN METIS_TAC [APPEND, APPEND_ASSOC, allItems]
);
    

val itemLhs = Define `itemLhs (item l r) = l`;
val itemFstRhs = Define `itemFstRhs (item l r) = FST r`;
val itemSndRhs = Define `itemSndRhs (item l r) = SND r`;

val ruleItems_mem = store_thm ("ruleItems_mem",
``∀it.MEM (item (itemLhs it) (itemFstRhs it++itemSndRhs it,[])) (ruleItems it)``,
HO_MATCH_MP_TAC ruleItems_ind THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [ruleItems, itemLhs, itemFstRhs, itemSndRhs] THEN
METIS_TAC [APPEND, APPEND_ASSOC]);

val allMemRuleItems = store_thm ("allMemRuleItems",
``∀it r1 r2.(itemSndRhs it = r1++r2) ⇒ MEM (item (itemLhs it) (itemFstRhs it++r1,r2)) (ruleItems it)``,
HO_MATCH_MP_TAC ruleItems_ind THEN SRW_TAC [] [ruleItems, itemFstRhs, itemSndRhs, itemLhs] THEN
Induct_on `r1` THEN SRW_TAC [] [] THEN METIS_TAC [APPEND, APPEND_NIL, APPEND_ASSOC]);


val memRuleAllItems = store_thm ("memRuleAllItems",
``∀l r rs.MEM (rule l r) rs ⇒ ∀r1 r2.(r=r1++r2) ⇒ MEM (item l (r1,r2)) (allItems rs)``,
Induct_on `rs` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [allItems] THENL[
`MEM (item (itemLhs (item l ([],r1++r2))) (itemFstRhs (item l ([],r1++r2)) ++r1,r2)) (ruleItems (item l ([],r1++r2)))`
by FULL_SIMP_TAC (srw_ss()) [allMemRuleItems, itemSndRhs] THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs, itemLhs, itemSndRhs],
Cases_on `h` THEN SRW_TAC [] [allItems]]);


val itemEqRuleExists = store_thm ("itemEqRuleExists",
 ``∀it.∀s q r.MEM (item s (q,r)) (ruleItems it) ⇒ (s=itemLhs it) ∧ (q++r = itemFstRhs it ++ itemSndRhs it)``,
HO_MATCH_MP_TAC ruleItems_ind THEN SRW_TAC [] [ruleItems, itemSndRhs, itemFstRhs, itemLhs] THEN
METIS_TAC [APPEND, APPEND_NIL, APPEND_ASSOC]);

 val memAllItemsRules = store_thm ("memAllItemsRules",
 ``∀rs s q r.MEM (item s (q,r)) (allItems rs) ⇒ MEM (rule s (q++r)) rs``,
Induct_on `rs` THEN SRW_TAC [] [allItems] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [allItems] THEN
IMP_RES_TAC itemEqRuleExists THEN
FULL_SIMP_TAC (srw_ss()) [itemLhs, itemFstRhs, itemSndRhs]);


val itemEqRuleEqAllItems = store_thm ("itemEqRuleEqAllItems",
``∀g.{x | itemEqRule g x} = (LIST_TO_SET (allItems (rules g)))``,
Induct_on `rules g` THEN SRW_TAC [] [EXTENSION, EQ_IMP_THM] THEN
Cases_on `x` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [allItems, itemEqRule] THEN
METIS_TAC [MEM, allItems, itemEqRule, memRuleAllItems, memAllItemsRules]);


val finite_itemEqRule = store_thm ("finite_itemEqRule",
``FINITE  (itemEqRule g)``,
ASSUME_TAC lemma THEN
`{x|P x} = P` by SRW_TAC [] [EXTENSION, IN_DEF] THEN
`itemEqRule g = {x | itemEqRule g x}` by SRW_TAC [] [EXTENSION, IN_DEF] THEN
ONCE_ASM_REWRITE_TAC [] THEN
METIS_TAC [itemEqRuleEqAllItems, SUBSET_FINITE, FINITE_LIST_TO_SET]);


val finite_allGrItls = store_thm ("finiteAllGrItls",
``∀g.FINITE (allGrammarItls g)``,
SRW_TAC [] [allGrammarItls, isGrammarItl, setc_flem, finite_itemEqRule]);


val prop_mem = store_thm ("prop_mem", 
``∀P l.MEM e (asNeighbours g itl l) ⇒ ∃e'.MEM e' l ∧ MEM e (asNeighbours g itl [e'])``,
Induct_on `l` THEN SRW_TAC [] [asNeighbours] THENL[
METIS_TAC [asNeighbours],
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e'`  THEN FULL_SIMP_TAC (srw_ss()) [asNeighbours] THEN METIS_TAC []]);




val validItl_evmem = store_thm ("validItl_evmem", 
``∀l.validItl g l = EVERY (itemEqRule g) l``,
Induct_on `l` THEN SRW_TAC [] [validItl] THEN
Cases_on `h` THEN Cases_on `p` THEN METIS_TAC [validItl, itemEqRule]);


val validItl_symNeighbour = store_thm ("validItl_symNeighbour", 
``∀itl.validItl g itl ⇒ EVERY (itemEqRule g) (symNeighbour g itl sym)``,
SRW_TAC [] [symNeighbour] THEN
`validItl g (iclosure g (moveDot itl sym))` by METIS_TAC [validItl_iclosure, validItl_md] THEN
METIS_TAC [validItl_evmem, rmDupes_prop]);


val symNeighbour_allDistinct = store_thm ("symNeighbour_allDistinct", 
``∀g itl sym.ALL_DISTINCT (symNeighbour g itl sym)``,
METIS_TAC [symNeighbour, alld_rmd]);



val ar1 = store_thm ("ar1", 
``∀a b c.a >=c ⇒ (a < b + (a-c) = 0 < b-c)``,
SRW_TAC [] [EQ_IMP_THM] THEN
DECIDE_TAC);




val (visit, visit_ind) = tprove (visit_defn,
WF_REL_TAC (`measure (\(g,sn,itl).CARD ((allGrammarItls g )DIFF (LIST_TO_SET sn)))`) THEN
SRW_TAC [] [] THEN
`MEM a (asNeighbours g itl (SET_TO_LIST (allSyms g)))` by METIS_TAC [diff_mem] THEN
`∃e'.MEM e' (SET_TO_LIST (allSyms g)) ∧ MEM a (asNeighbours g itl [e'])` by METIS_TAC [prop_mem] THEN
FULL_SIMP_TAC (srw_ss()) [asNeighbours] THEN
`EVERY (itemEqRule g) a` by METIS_TAC [validItl_symNeighbour] THEN
`ALL_DISTINCT a` by METIS_TAC [symNeighbour_allDistinct] THEN
`isGrammarItl g a` by METIS_TAC [isGrammarItl] THEN
`a IN (allGrammarItls g)` by SRW_TAC [] [allGrammarItls, EXTENSION] THEN
`~ (a IN LIST_TO_SET sn)` by METIS_TAC [diff_mem, mem_in] THEN
SRW_TAC [] [diff_DIFF] THEN
`FINITE (allSyms g)` by METIS_TAC [FINITE_LIST_TO_SET, finiteAllSyms] THEN
`FINITE (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF set sn)` by METIS_TAC [FINITE_LIST_TO_SET, FINITE_DIFF] THEN
`FINITE ((set sn) UNION (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF set sn))` by METIS_TAC [FINITE_LIST_TO_SET, FINITE_DIFF,
FINITE_UNION] THEN
`FINITE (allGrammarItls g)` by METIS_TAC [finite_allGrItls] THEN
FULL_SIMP_TAC (srw_ss()) [CARD_DIFF, FINITE_LIST_TO_SET, FINITE_DIFF, finite_allGrItls, FINITE_UNION] THEN SRW_TAC [] [] THENL[
`(symNeighbour g itl e') IN (allGrammarItls g INTER
       (set sn UNION
        (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF set sn)))` by FULL_SIMP_TAC (srw_ss()) [INTER_DEF] THEN
`~((symNeighbour g itl e') IN (allGrammarItls g INTER set sn))` by METIS_TAC [not_in_inter, mem_in, finite_allGrItls] THEN
`symNeighbour g itl e' IN (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(symNeighbour g itl e' IN (set sn))` by METIS_TAC [mem_in] THEN
`~((set sn) = (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn)))` by METIS_TAC [] THEN
`(CARD (allGrammarItls g) - CARD (allGrammarItls g INTER set sn)) > 0` by METIS_TAC [inter_card_less, INTER_COMM, finite_allGrItls] THEN
`(CARD (allGrammarItls g)) >= CARD (allGrammarItls g INTER set sn)` by DECIDE_TAC THEN
SRW_TAC [] [ar1] THEN
`(set sn) SUBSET (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`(set sn) PSUBSET (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by METIS_TAC [PSUBSET_DEF] THEN
`CARD (set sn) < CARD (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET, FINITE_UNION, FINITE_DIFF] THEN
`CARD (set sn INTER (allGrammarItls g)) < CARD (((set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
            set sn)) INTER (allGrammarItls g)))` by METIS_TAC [mem_in, card_same_inter, FINITE_UNION, FINITE_DIFF, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (arith_ss) [INTER_COMM],

`CARD (allGrammarItls g) - CARD ((allGrammarItls g) INTER (LIST_TO_SET sn)) > 0` 
by METIS_TAC [inter_card_less, finite_allGrItls, mem_in] 
THEN
DECIDE_TAC]);

val _ = save_thm ("visit",visit);
val _ = save_thm ("visit_ind",visit_ind);


val slrML4Sym = Define `
(slrML4Sym g [] sym = SOME (sgoto g, reduce g)) ∧
(slrML4Sym g (i::itl) sym = 
let
s = sgoto g i sym 
in
let
r = reduce g i (ts2str sym)
in
case (s,r) of 
                     ([],[]) -> slrML4Sym g itl sym
                    || ([],[v12]) -> slrML4Sym g itl sym
                    || ([],v12::v16::v17) -> NONE
                    || (v8::v9,[]) -> slrML4Sym g itl sym
                    || (v8::v9,[v20]) -> NONE
                    || (v8::v9,v20::v26::v27) -> NONE)`;


val slrML = Define `
(slrML g itl [] = SOME (sgoto g, reduce g)) ∧
(slrML g itl (sym::rst) = 
if (slrML4Sym g itl sym = NONE) then NONE else slrML g itl rst)`;



val findItemInRules = Define 
`(findItemInRules (item l1 (r1,[])) [] = F) ∧
(findItemInRules (item l1 (r1,[])) ((rule l2 r2)::rst) = T) ∧
(findItemInRules (item l1 (r1,[])) (_::rst) = 
 findItemInRules (item l1 (r1,[])) rst) ∧
(findItemInRules _ _ = F)`;

val itemEqRuleList_defn = Hol_defn "itemEqRuleList_defn"
`(itemEqRuleList [] [] = T) ∧
(itemEqRuleList [] _ = T) ∧
(itemEqRuleList _ [] = F) ∧
(itemEqRuleList l1 l2 = 
 if ~(LENGTH l1 = LENGTH l2) then F
 else
     if (findItemInRules (HD l1) l2) then itemEqRuleList (TL l1) l2
     else F)`;


val (itemEqRuleList,itemEqRuleList_ind) = tprove (itemEqRuleList_defn,
WF_REL_TAC (`measure (\(l1,l2).LENGTH l1)`) THEN	
SRW_TAC [] []);

		
val getState = Define 
`(getState (sg,red) (itl:('nts,'ts)item list) (sym:('nts,'ts) symbol) = 
             let 
                newitl = sg itl sym and
                rl =  (red itl (ts2str sym))
	     in
			case (newitl,rl) of ([],[]) -> NA 
			|| ([],(y::ys)) -> if (LENGTH rl = 1) then REDUCE  (HD rl) 
					   else NA 
			|| ((x::xs),[]) -> GOTO newitl
			|| ((x::xs),(y::ys)) -> if (itemEqRuleList (x::xs) (y::ys))
						    then REDUCE (HD rl) else NA)`;





(* three output options:
    NONE : failed to terminate
    SOME NONE : failed, but terminated (i.e., parse error)
    SOME (SOME s) : succeeded, and result is s
*)

(* parse :: machine -> (symbol list, (state,ptree) list) -> (symbol list, (state, ptree) list) option *)

val md_append = store_thm ("md_append", 
``∀l1 l2.moveDot (l1++l2) sym = moveDot l1 sym ++ moveDot l2 sym``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [moveDot] THEN
Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` THEN Cases_on `h'=sym` THEN
FULL_SIMP_TAC (srw_ss()) [moveDot]);


val iclosure_mem = store_thm ("iclosure_mem",
``∀g l.MEM e l ⇒ MEM e (iclosure g l)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, LET_THM] THEN
METIS_TAC [rmd_r2, iclosure1_mem, MEM]);

val sgoto_mem = store_thm ("sgoto_mem", 
``MEM (item s (q,sym::t)) itl ⇒ (MEM (item s (q++[sym],t)) (sgoto ag itl sym))``,
SRW_TAC [] [sgoto, nextState] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, md_append, moveDot] THEN
METIS_TAC [rgr_r9eq, iclosure_mem]);

val reduce_append = store_thm ("reduce_append",
``reduce g (l1++l2) sym = reduce g l1 sym ++ reduce g l2 sym``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [reduce] THEN
Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` THEN
METIS_TAC [APPEND, CONS, reduce]);




val trans_snoc = store_thm("trans_snoc",
  ``∀s. 
      trans ag (s, vp ++ [h]) =
        case trans ag (s, vp) of 
           NONE -> NONE
        || SOME s' -> (case moveDot s' h of [] -> NONE 
                                        || x -> SOME (iclosure ag x))``,
  Induct_on `vp` THEN SRW_TAC [][trans] THEN 
  Cases_on `moveDot s h'` THEN SRW_TAC [][]);


val initProds2Items_append = store_thm ("initProds2Items_append",
``∀r1 r2.(initProds2Items s (r1 ++ r2) = 
 initProds2Items s r1 ++ initProds2Items s r2)``,
Induct_on `r1` THEN Induct_on `r2` THEN
SRW_TAC [] [initProds2Items] THEN
Cases_on `h'` THEN SRW_TAC [] [initProds2Items] THEN
METIS_TAC []);
 
val memInitProds = store_thm ("memInitProds",
``MEM (rule (startSym ag) rhs) (rules ag) ⇒ 
    MEM (item (startSym ag) ([],rhs)) (initItems ag (rules ag))``,
SRW_TAC [] [initItems, rgr_r9eq] THEN
SRW_TAC [] [initProds2Items_append, initProds2Items] THEN
METIS_TAC [iclosure_mem, MEM, MEM_APPEND, rgr_r9eq]);


val sublemma = store_thm("sublemma",
  ``∀pfx sfx. 
      NRC (rderives g) n [NTS st] (pfx ++ [NTS nt] ++ sfx) ∧ 
      0 < n ⇒
      ∃m1 m2 pfx1 pfx2 sfx1 sfx2 sfx2' nt'. 
          m1 < n ∧ m2 < n ∧
          NRC (rderives g) m1 [NTS st] 
              (pfx1 ++ [NTS nt'] ++ sfx1) ∧
          MEM (rule nt' (pfx2 ++ [NTS nt] ++ sfx2)) (rules g) ∧
          EVERY isTmnlSym sfx1 ∧
          NRC (rderives g) m2 
              (pfx1 ++ pfx2 ++ [NTS nt] ++ sfx2 ++ sfx1) 
              (pfx1 ++ pfx2 ++ [NTS nt] ++ sfx2' ++ sfx1) ∧
          (pfx = pfx1 ++ pfx2) ∧ (sfx = sfx2' ++ sfx1)``,

  Induct_on `n` THEN SRW_TAC [][NRC_SUC_RECURSE_LEFT] THEN
  Cases_on `0<n` THENL[
    `∃pfx0 sfx0 Nt1 rhs.
        (z=pfx0++[NTS Nt1]++sfx0) ∧
        (pfx++[NTS nt]++sfx = pfx0++rhs++sfx0) ∧
        MEM (rule Nt1 rhs) (rules g) ∧
        EVERY isTmnlSym sfx0` 
      by METIS_TAC [rderives_def] THEN
    SRW_TAC [] [] THEN
    Cases_on `IS_PREFIX pfx0 pfx` THENL[
      Cases_on `pfx0=pfx` THEN1
        (SRW_TAC [] [] THEN
        Cases_on `rhs` THEN
        SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [] THENL[
          `sfx0=[NTS nt]++sfx` 
             by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
          SRW_TAC [] [] THEN
          FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

          (* rhs is not empty *)
          `[NTS nt] ++ sfx = h::t ++ sfx0`
             by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN 
          FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN 
          MAP_EVERY Q.EXISTS_TAC [`n`, `0`, `pfx`, `[]`, 
                                  `sfx0`, `t`, `t`, `Nt1`] THEN 
          SRW_TAC [][]
        ]) THEN

        (* pfx \neq pfx0 *)
        `∃t. pfx0 = pfx ++ NTS nt :: t`
           by (`∃l. pfx0 = pfx ++ l` 
                 by METIS_TAC [IS_PREFIX_APPEND] THEN 
               SRW_TAC [][] THEN 
               `∃hl tl. l = hl :: tl`
                  by (Cases_on `l` THEN 
                      FULL_SIMP_TAC (srw_ss()) []) THEN 
               SRW_TAC [][] THEN 
               METIS_TAC [APPEND_11, APPEND, APPEND_ASSOC,
                          CONS_11]) THEN 
        SRW_TAC [][] THEN
        `NRC (rderives g) n [NTS st]
             (pfx ++ [NTS nt] ++ (t ++ [NTS Nt1] ++ sfx0))`
           by METIS_TAC [APPEND_ASSOC, APPEND] THEN 
        `∃m1 m2 p1 p2 s1 s2 s2' nt'.
            m1 < n ∧ m2 < n ∧ 
            NRC (rderives g) m1 [NTS st] (p1 ++ [NTS nt'] ++ s1) ∧
            MEM (rule nt' (p2 ++ [NTS nt] ++ s2)) (rules g) ∧
            EVERY isTmnlSym s1 ∧
            NRC (rderives g) m2 
                (p1 ++ p2 ++ [NTS nt] ++ s2 ++ s1)
                (p1 ++ p2 ++ [NTS nt] ++ s2' ++ s1) ∧
            (pfx = p1 ++ p2) ∧ 
            (t ++ [NTS Nt1] ++ sfx0 = s2' ++ s1)`
           by METIS_TAC [] THEN 
        `isSuffix s1 sfx0`
           by (`isSuffix s1 sfx0 ∨ isSuffix sfx0 s1`
                 by METIS_TAC [append_eq_imp_sfx, APPEND_ASSOC] THEN
               `∃foo. s1 = foo ++ sfx0` 
                 by METIS_TAC [isSuffix_APPEND] THEN 
               Cases_on `foo` THEN SRW_TAC [][] THEN 
               `s2' ++ h::t' = t ++ [NTS Nt1]`
                  by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
               `LAST (h::t') = NTS Nt1` by METIS_TAC [NOT_CONS_NIL, last_elem, 
						      last_append] THEN
               `MEM (LAST (h::t')) (h::t')`
                 by METIS_TAC [MEM_APPEND, APPEND_FRONT_LAST, 
                               MEM] THEN 
		 `isWord [NTS Nt1]` by 
		 METIS_TAC [APPEND_FRONT_LAST, NOT_CONS_NIL, EVERY_MEM, 
			    EVERY_APPEND] THEN
		 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
        `∃sf1. sfx0 = sf1 ++ s1` by METIS_TAC [isSuffix_APPEND] THEN 
        SRW_TAC [][] THEN 
        MAP_EVERY Q.EXISTS_TAC [`m1`, `SUC m2`, 
                                `p1`, `p2`, `s1`, `s2`, 
                                `t ++ rhs ++ sf1`, 
                                `nt'`] THEN 
        SRW_TAC [ARITH_ss][] THENL [
          SRW_TAC [][NRC_SUC_RECURSE_LEFT] THEN 
          Q.EXISTS_TAC `p1 ++ p2 ++ [NTS nt] ++ s2' ++ s1` THEN 
          SRW_TAC [][] THEN 
          METIS_TAC [APPEND, APPEND_ASSOC],

          FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11, 
                                 APPEND, CONS_11]
        ],

      
      `IS_PREFIX pfx pfx0 ∨ IS_PREFIX pfx0 pfx`
	  by METIS_TAC [append_eq_imp_pfx, APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
      SRW_TAC [] [] THEN
      `l++[NTS nt]++sfx = rhs++sfx0` 
	  by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      Q_TAC SUFF_TAC `∃sf1.(sfx = sf1 ++ sfx0)`
      THENL[
	    SRW_TAC [] [] THEN
	    `rhs=l++[NTS nt]++sf1` 
		by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    SRW_TAC [] [] THEN
            MAP_EVERY Q.EXISTS_TAC [`n`, `0`, 
                                    `pfx0`, `l`, `sfx0`, `sf1`, 
                                    `sf1`, 
                                `Nt1`] THEN 
            SRW_TAC [ARITH_ss][],
	    
	`(l=rhs) ∨
         (∃p s.(rhs=l++[NTS nt]++p) 
          ∧ (sfx=p++s)) ∨
         (∃p s.(l=p++s) ∧
            (rhs=p))` by METIS_TAC [listCompLens] THEN
	SRW_TAC [] []
	 THENL[
	       `[NTS nt]++sfx = sfx0` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	       SRW_TAC [] [] THEN
	       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
	       
	       METIS_TAC [APPEND_11, APPEND_ASSOC],

	       `s++[NTS nt]++sfx = sfx0` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	       SRW_TAC [] [] THEN
	       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
	       ]
	    ]],
      

    `n=0`by DECIDE_TAC THEN
    SRW_TAC [] [] THEN
    FULL_SIMP_TAC (srw_ss()) [NRC] THEN
    SRW_TAC [] [] THEN
    MAP_EVERY Q.EXISTS_TAC [`0`, `0`, `[]`, `pfx`, `[]`, `sfx`, 
			      `sfx`, `st`] THEN 
    SRW_TAC [][] THEN 
    FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN 
    METIS_TAC [APPEND_NIL]
    ]);


val iclosure1_append = store_thm ("iclosure1_append",
``∀l1 l2.iclosure1 g (l1 ++ l2) = iclosure1 g l1 ++ iclosure1 g l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [iclosure1] THEN
Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` 
THENL[
      SRW_TAC [] [iclosure1],

      Cases_on `h'` THEN SRW_TAC [] [iclosure1] THEN
      METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL]
      ]
);


val getItems_append = store_thm ("getItems_append",
``∀l1 l2.getItems (l1++l2) N  = getItems l1 N ++ getItems l2 N``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [getItems] THEN
Cases_on `h'` THEN SRW_TAC [] [getItems]);


  
val iclosureNtGen = store_thm ("iclosureNtGen",
``∀ag l r1.MEM (item lhs (r1,NTS N::r2)) (iclosure ag l) ⇒ 
 ∀rhs.MEM (rule N rhs) (rules ag) ⇒
MEM (item N ([],rhs)) (iclosure ag l)``,
HO_MATCH_MP_TAC iclosure_ind THEN 
SRW_TAC [] [iclosure, LET_THM] THEN
`(item lhs (r1,NTS N::r2)) IN set 
(rmDupes (iclosure1 ag (rmDupes (v2::v3))))` by 
FULL_SIMP_TAC (srw_ss()) [] THEN
`(item lhs (r1,NTS N::r2)) IN set (rmDupes (v2::v3))` by METIS_TAC [] THEN
`MEM (item lhs (r1,NTS N::r2)) (SET_TO_LIST (set (rmDupes (v2::v3))))` by 
METIS_TAC [FINITE_LIST_TO_SET, MEM_SET_TO_LIST, SET_TO_LIST_IN_MEM] THEN
`MEM (item lhs (r1,NTS N::r2)) (rmDupes (v2::v3))` by METIS_TAC [stl_mem, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, iclosure1_append] THEN
`rmDupes (iclosure1 ag (rmDupes (v2::v3))) = 
rmDupes (iclosure1 ag (r1''' ++ [item lhs (r1,NTS N::r2)] ++ r2'''))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_append, iclosure1] THEN
`getItems (rules ag) N  = getItems (r1' ++ [rule N rhs] ++ r2') N` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [getItems_append, getItems] THEN
METIS_TAC [rgr_r9eq, APPEND, rmd_r2, APPEND_ASSOC]);

val transOutMem = store_thm("transOutMem",
``∀g s s0 vp1 nt sfx nt'.
  (trans g (iclosure g s0,vp1) = SOME s) ⇒
  MEM (item nt' (r1,NTS nt::sfx)) s ⇒
  MEM (rule nt rhs) (rules g) ⇒
  MEM (item nt ([],rhs)) s``,
Induct_on `vp1` THEN SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [trans] THEN
SRW_TAC [] []
THENL[
      METIS_TAC [iclosureNtGen],

      Cases_on `moveDot (iclosure g s0) h` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      METIS_TAC []
      ]);


val transExists = store_thm ("transExists",
``∀ nt r1 vp rst s.MEM (item nt (r1,vp++rst)) s ⇒
  ∃s'.(trans g (s, vp) = SOME s') ∧ 
       MEM (item nt (r1++vp, rst)) s'``,
Induct_on `vp` THEN SRW_TAC [] [trans] THEN
`~(moveDot s h = [])` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, md_append, moveDot] THEN
Cases_on `moveDot r1' h ++ [item nt (r1 ++ [h],vp ++ rst)] ++
         moveDot r2 h` THEN
      METIS_TAC [MEM, MEM_APPEND]) THEN
Cases_on `moveDot s h` THEN SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`nt`, `r1++[h]`, `rst`,
                `iclosure g (h'::t)`] MP_TAC ) THEN
SRW_TAC [] [] THEN
`MEM (item nt (r1 ++ [h],vp ++ rst)) (h'::t)` by (SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [md_append, moveDot] THEN
METIS_TAC [MEM, MEM_APPEND, rgr_r9eq]) THEN
METIS_TAC [c1, iclosure_mem]);
      

val transSeq = store_thm ("transSeq",
``∀s s' vp sp' s''.
  (trans g (iclosure g s, vp) = SOME s') ⇒
  (trans g (s',vp') = SOME s'') ⇒
  (trans g (iclosure g s, vp++vp') = SOME s'')``,
Induct_on `vp` THEN SRW_TAC [] [trans] THEN
Cases_on `moveDot (iclosure g s) h` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) []
);


val ic1Delete = store_thm 
("ic1Delete",
``∀e h l.~(e=h) ⇒ ~(MEM e l) ⇒
   MEM e (iclosure1 g l) ⇒ 
   MEM e (iclosure1 g [h]) ∨ (MEM e (iclosure1 g (delete h l)))``,
Induct_on `l` THEN SRW_TAC [] [delete_def,iclosure1] THEN
`(iclosure1 g (h::l) = iclosure1 g [h] ++ iclosure1 g l)`
    by METIS_TAC [iclosure1_append,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [iclosure1_append,APPEND,MEM_APPEND]);


val ic1Delete2 = store_thm 
("ic1Delete2",
``∀e h l.~(e=h) ⇒ ~(MEM e (delete h l)) ⇒
   MEM e (iclosure1 g (delete h l)) ⇒ 
   MEM e (iclosure1 g [h]) ∨ (MEM e (iclosure1 g l))``,
Induct_on `l` THEN SRW_TAC [] [delete_def,iclosure1] THEN
`(iclosure1 g (h::l) = iclosure1 g [h] ++ iclosure1 g l)`
    by METIS_TAC [iclosure1_append,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [iclosure1_append,APPEND,MEM_APPEND]);


val iclosure1RmdMem =
store_thm ("iclosure1RmdMem",
``∀e l.MEM e (iclosure1 g l) = MEM e (iclosure1 g (rmDupes l))``,

Induct_on `l` THEN SRW_TAC [] [iclosure1,rmDupes,EQ_IMP_THM] THEN
`(iclosure1 g (h::l) = iclosure1 g [h] ++ iclosure1 g l)`
    by METIS_TAC [iclosure1_append,APPEND] THEN
`(iclosure1 g (h::rmDupes (delete h l)) =
 iclosure1 g [h] ++ iclosure1 g (rmDupes (delete h l)))`
	  by METIS_TAC [iclosure1_append,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
Cases_on `e=h` THEN
SRW_TAC [][]
THENL[
      METIS_TAC [iclosure1_mem,MEM],

      SRW_TAC [] [rmd_del] THEN
      Cases_on `MEM e l`
      THENL[
	    METIS_TAC [delete_mem_list,rmd_mem_list,iclosure1_mem],

	    
	    `~(MEM e (delete h (rmDupes l)))`
		by METIS_TAC [rmd_mem_list,delete_mem_list] THEN
	    METIS_TAC [ic1Delete,rmd_mem_list,delete_mem_list]
	    ],

      METIS_TAC [iclosure1_mem,MEM],

      Cases_on `MEM e l`
      THENL[
	    METIS_TAC [delete_mem_list,rmd_mem_list,iclosure1_mem],

	    `~(MEM e (delete h (rmDupes l)))`
		by METIS_TAC [rmd_mem_list,delete_mem_list] THEN
	    `~MEM e (rmDupes (delete h l))` by
	    METIS_TAC [rmd_mem_list,delete_mem_list] THEN
	    `∀e h l.
            ~(e = h) ⇒
            ~MEM e l ⇒
            MEM e (iclosure1 g l) ⇒
            MEM e (iclosure1 g [h]) ∨ MEM e (iclosure1 g (delete h l))`
		by METIS_TAC [ic1Delete] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`e`,`h`,`rmDupes (delete h l)`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [rmd_del] THEN

	    `(delete h (delete h (rmDupes l))) = delete h (rmDupes l)`
		by METIS_TAC [delete_twice] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [rmd_mem_list,iclosure1_mem,delete_mem_list,ic1Delete2]
	    ]
      ]);


val ic1ImpIcMem =
store_thm ("ic1ImpIcMem",
``∀e l.MEM e (iclosure1 g l) ⇒ MEM e (iclosure g l)``,
Induct_on `l` THEN SRW_TAC [] [iclosure,iclosure1,LET_THM] THEN
METIS_TAC [iclosure1RmdMem,rmd_mem_list,iclosure_mem]);


val icImpIcTwice =
store_thm ("icImpIcTwice",
``∀g l.MEM e (iclosure g l) ⇒ MEM e (iclosure g (iclosure g l))``,
HO_MATCH_MP_TAC iclosure_ind THEN
SRW_TAC [][iclosure,LET_THM] THEN
METIS_TAC [iclosure_mem]);

val icEqIc1 = store_thm
("icEqIc1",
``∀g l.(set (rmDupes l) = set (rmDupes (iclosure1 g (rmDupes l)))) ⇒
  (rmDupes (iclosure1 g (rmDupes l)) = iclosure g l)``,
HO_MATCH_MP_TAC iclosure_ind THEN
SRW_TAC [] [iclosure,iclosure1] THEN
FULL_SIMP_TAC (srw_ss()) [rmDupes,iclosure1,LET_THM]);

val _ = Globals.linewidth := 60

val forallItem = store_thm ("forallItem",
``(∀h.P h) = ∀N l1 l2.P (item N (l1,l2))``,
SRW_TAC [][EQ_IMP_THM] THEN
Cases_on `h` THEN
Cases_on `p` THEN SRW_TAC [][]);

val forallRule = store_thm ("forallRule",
``(∀h.P h) = ∀N rhs.P (rule N rhs)``,
SRW_TAC [][EQ_IMP_THM] THEN
Cases_on `h` THEN
SRW_TAC [][]);



val getItemsInRule = 
store_thm ("getItemsInRule",
``∀l N l1 l2 nt.MEM (item N (l1,l2)) (getItems l nt) =
  (N=nt) ∧ MEM (rule N (l1++l2)) l ∧ (l1=[])``,
Induct_on `l` THEN 
ASM_SIMP_TAC (srw_ss()) [forallRule,getItems] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_NIL]);


val iclosure1MemType = store_thm
("iclosure1MemType",
``∀e l.MEM e (iclosure1 g l) =
  MEM e l ∨ 
∃N M p s r.MEM (rule N r) (rules g) ∧
(MEM (item M (p,NTS N::s)) l) ∧
 (e=item N ([],r)) ``,

Induct_on `l` THEN 
ASM_SIMP_TAC (srw_ss()) [iclosure1,forallItem] THEN
SRW_TAC [][] THEN
Cases_on `l2` THEN SRW_TAC [] [iclosure1] THEN1
 METIS_TAC [] THEN

 Cases_on `h` THEN SRW_TAC [] [iclosure1] THEN
 SRW_TAC [] [getItemsInRule] THEN
 METIS_TAC [APPEND_NIL]);


val iclosure' = prove(
  ``iclosure g l = 
       let ril = rmDupes l in
       let al = rmDupes (iclosure1 g ril) in
         if ~(set ril = set al) then iclosure g al else al``,
  Cases_on `l` THEN 
  SRW_TAC [][iclosure, LET_THM, rmDupes, iclosure1]);

val iclosure_NIL = store_thm(
  "iclosure_NIL",
  ``iclosure g [] = []``,
  SRW_TAC [][iclosure]);
val _ =export_rewrites ["iclosure_NIL"];

val set_rmDupes = store_thm(
  "set_rmDupes",
  ``set (rmDupes l) = set l``,
  MATCH_ACCEPT_TAC (GSYM rmDupes_lts));
val _ = export_rewrites ["set_rmDupes"];
  

val iclosure_ind' = prove(
  ``∀P. (∀g l. (∀ril al. (ril = rmDupes l) ∧
                         (al = rmDupes (iclosure1 g ril)) ∧
                         ~(set ril = set al) ⇒ 
                         P g al) ⇒
               P g l) ⇒
        ∀v v1. P v v1``,
  NTAC 2 STRIP_TAC THEN 
  HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [][] THEN 
  FIRST_X_ASSUM MATCH_MP_TAC THEN 
  SIMP_TAC (srw_ss())[rmDupes, iclosure1]);


val ic1EqSet = store_thm
("ic1EqSet",
``∀l l'.(set l = set l') ⇒
((set (iclosure1 g l)) = set (iclosure1 g l'))``,
SRW_TAC [][ EXTENSION,EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1MemType] THEN
METIS_TAC []);

val ic1EqSetRmd = store_thm
("ic1EqSetRmd",
``∀l l'.(set l = set l') ⇒
((set (iclosure1 g l)) = set (iclosure1 g (rmDupes l')))``,
SRW_TAC [] [] THEN
SRW_TAC [][ EXTENSION,EQ_IMP_THM] THEN
`((set (iclosure1 g l)) = set (iclosure1 g l'))`
    by METIS_TAC [ic1EqSet] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [iclosure1RmdMem]);


val icTwiceImpIc =
store_thm ("icTwiceImpIc",
``∀g l.MEM e (iclosure g (iclosure g l)) ⇒ 
	  MEM e (iclosure g l)``,
HO_MATCH_MP_TAC iclosure_ind' THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN 
MP_TAC iclosure' THEN 
DISCH_THEN (fn th => REWRITE_TAC [th]) THEN 
SRW_TAC [][LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) 
	      [Once iclosure', LET_THM, rmDupes_twice] THEN 
Q.ABBREV_TAC `l = v2::v3` THEN 
markerLib.RM_ALL_ABBREVS_TAC THEN 
IMP_RES_TAC icEqIc1 THEN
FULL_SIMP_TAC (srw_ss()) [rmd_mem_list, Once iclosure', 
			  LET_THM, rmDupes_twice] THEN
SRW_TAC [] [iclosure1MemType,rmd_mem_list] THEN
Cases_on `~(set (iclosure1 g (rmDupes l)) =
            set
                (iclosure1 g
			   (rmDupes (iclosure1 g (rmDupes l)))))` THEN
SRW_TAC [] []
THENL[
      METIS_TAC [ic1EqSetRmd],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.ABBREV_TAC `l'=(iclosure1 g (rmDupes l))` THEN
      METIS_TAC [ic1EqSet,mem_in,iclosure1RmdMem,rmd_mem_list]
      ]);

val iclosureTwice =
store_thm ("iclosureTwice",
``∀g l.set (iclosure g (iclosure g l)) = set (iclosure g l)``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM] THEN
 METIS_TAC [icTwiceImpIc,icImpIcTwice]);


val mdMem = store_thm ("mdMem",
``∀e itl sym.MEM e (moveDot itl sym) ⇒  
∃l r1 r2.(e=item l (r1++[sym],r2)) 
∧ (MEM (item l (r1,sym::r2)) itl)``,
Induct_on `itl` THEN SRW_TAC [] [moveDot] THEN
`moveDot (h::itl) sym = 
moveDot [h] sym ++ moveDot itl sym` by METIS_TAC [md_append, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] 
THENL[
      Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
      FULL_SIMP_TAC (srw_ss()) [moveDot] THEN
      Cases_on `h=sym` THEN FULL_SIMP_TAC (srw_ss()) [],
      METIS_TAC []]);


val mdMemExists = store_thm ("mdMemExists",
``∀itl r1 r2 h.MEM (item lhs (r1,h::r2)) itl ⇒
  MEM (item lhs (r1++[h],r2)) (moveDot itl h)``,
SRW_TAC [][rgr_r9eq,md_append]  THEN
SRW_TAC [] [md_append,moveDot] THEN
METIS_TAC [APPEND_NIL]);

val mdSetEq = store_thm
("mdSetEq",
``∀l l' h.(set l = set l') ⇒
  (set (moveDot l h) = set (moveDot l' h))``,
Induct_on `l` THEN SRW_TAC [][moveDot,EQ_IMP_THM,EXTENSION] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      METIS_TAC [mdMem],

      IMP_RES_TAC mdMem THEN
      SRW_TAC [][] THEN
      `MEM (item l'' (r1,h'::r2)) l'` 
	  by METIS_TAC [MEM] THEN
      METIS_TAC [mdMemExists],

      IMP_RES_TAC mdMem THEN
      SRW_TAC [][] THEN
      METIS_TAC [mdMem,mdMemExists,MEM]
      ]);
      

val iclosureMemIc1 = store_thm
("iclosureMemIc1",
``∀g l.MEM e (iclosure g l) =
  MEM e l ∨ ∃e'.MEM e' l ∧ MEM e (iclosure g [e'])``,
MAGIC);
(*
HO_MATCH_MP_TAC iclosure_ind' THEN

SRW_TAC [][EQ_IMP_THM] THEN
THENL[
      Cases_on `MEM e l` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rmd_mem_list,
				iclosure1MemType,
				Once iclosure',LET_THM] THEN
      Cases_on `~(set l = set (iclosure1 g (rmDupes l)))` THEN
      FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    


	    ]


      METIS_TAC [iclosure_mem],

      METIS_TAC [iclosure_mem],
      


      THENL[	    
	    SRW_TAC [][Once iclosure',LET_THM] THEN
	    FULL_SIMP_TAC (srw_ss()) [rmd_mem_list,iclosure1MemType] THEN
	    SRW_TAC [][] 	    
	    THENL[
		  Q.EXISTS_TAC `item M (p,NTS N::s)` THEN
		  SRW_TAC [][] THEN
		  SRW_TAC [] [rmDupes,delete_def,iclosure1,getItems,getItems_append] THEN
		  `∃r1 r2.rules g = r1++[rule N r]++r2`
		      by METIS_TAC [rgr_r9eq] THEN
		  SRW_TAC [][getItems_append,getItems] THEN
		  METIS_TAC [iclosure_mem,rmd_mem_list,MEM,MEM_APPEND],

		  Cases_on `~({e'} = set (iclosure1 g (rmDupes [e'])))` THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [],

		  Cases_on `~({item N ([],r)} =
			      set (iclosure1 g (rmDupes [item N ([],r)])))` THEN
      		  FULL_SIMP_TAC (srw_ss()) []
                  THENL[
			Q.EXISTS_TAC `item M (p,NTS N::s)` THEN
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) [rmDupes,delete_def,iclosure1] THEN
			`∃r1 r2.rules g = r1++[rule N r]++r2`
			    by METIS_TAC [rgr_r9eq] THEN
			SRW_TAC [][getItems_append,getItems] THEN
			MAGIC,
			
			MAGIC
			]
		  ],

      
      FULL_SIMP_TAC (srw_ss()) [Once iclosure',LET_THM] THEN
      FULL_SIMP_TAC (srw_ss()) [rmd_mem_list,iclosure1MemType] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `item M (p,NTS N::s)` THEN
      SRW_TAC [][] THEN
      SRW_TAC [] [rmDupes,delete_def,iclosure1,getItems,getItems_append] THEN
      `∃r1 r2.rules g = r1++[rule N r]++r2`
	  by METIS_TAC [rgr_r9eq] THEN
      SRW_TAC [][getItems_append,getItems] THEN
      METIS_TAC [iclosure_mem,rmd_mem_list,MEM,MEM_APPEND]
      ])
*)


val iclosure_APPEND = 
store_thm ("iclosure_APPEND",
``MEM e (iclosure g (l1++l2)) =
  (MEM e (l1++l2) ∨ MEM e (iclosure g l1) ∨
  MEM e (iclosure g l2))``,
SRW_TAC [][EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [Once iclosureMemIc1] THEN
METIS_TAC [iclosure_mem,iclosureMemIc1]);

val iclosureSetEq = store_thm 
("iclosureSetEq",
``∀g l l'.(set l = set l') ⇒
  (set (iclosure g l) = set (iclosure g l'))``,
SRW_TAC [][EXTENSION,EQ_IMP_THM,Once iclosureMemIc1]
THENL[
      METIS_TAC [iclosure_mem],

      `MEM e' l'` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
      METIS_TAC [iclosure_APPEND,rgr_r9eq,iclosure_mem,APPEND_ASSOC],

      METIS_TAC [iclosure_mem,iclosureMemIc1]
      ]);


val transIcIcImpIc = store_thm (
"transIcIcImpIc",
``∀g l l' p s.(set l = set l') ⇒
(trans g (l,p) = SOME s) ⇒
  ∃s'.(trans g (l',p) = SOME s')
∧ (set s = set s')``,
Induct_on `p` THEN SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [iclosure,trans],

      FULL_SIMP_TAC (srw_ss()) [trans] THEN
      Cases_on `moveDot l h` THEN
      Cases_on `moveDot l' h` THEN
      FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    METIS_TAC [mem_in,MEM,mdSetEq],

	    `set (h'::t) = set (h''::t')`
	    by METIS_TAC [mdSetEq] THEN
	    `set (iclosure g (h'::t))=
             set (iclosure g (h''::t'))` 
		by METIS_TAC [iclosureSetEq] THEN
	    METIS_TAC []
	    ]]);


val transSeqIcGen = store_thm ("transSeqIcGen",
``∀s s' vp sp' s''.
  (trans g (iclosure g s, vp) = SOME s') ⇒
  (trans g (iclosure g s',vp') = SOME s'') ⇒
  ∃s'''.(trans g (iclosure g s, vp++vp') = SOME s''')
  ∧ (set s''' = set s'')``,
Induct_on `vp` THEN SRW_TAC [] [trans] 
THENL[
      METIS_TAC [transIcIcImpIc,iclosureTwice],

      Cases_on `moveDot (iclosure g s) h` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) []
      ]);


val transShiftExists = store_thm ("transShiftExists",
``∀s s0 r1 vp1 vp2 nt sfx rhs.
   (trans g (iclosure g s0,vp1) = SOME s) ⇒
    MEM (item nt' (r1,vp2++[NTS nt]++sfx)) s ⇒
    MEM (rule nt rhs) (rules g) ⇒
    ∃s'.(trans g (iclosure g s0, vp1++vp2) = SOME s') ∧
        MEM (item nt ([],rhs)) s'``,
Induct_on `vp2` THEN SRW_TAC [] []
THENL[
      METIS_TAC [transOutMem],

      `∃s'.(trans g (iclosure g s,h::vp2) = SOME s') ∧
         MEM (item nt' (r1++[h]++vp2,[NTS nt]++sfx)) s'` by 
      (SRW_TAC [] [] THEN
      SRW_TAC [] [trans] THEN
      `MEM (item nt' (r1,h::(vp2 ++ [NTS nt] ++ sfx))) (iclosure g s)`
      by METIS_TAC [iclosure_mem]) 
      THENL[
	    `MEM (item nt' (r1++[h],(vp2 ++ [NTS nt] ++ sfx)))
              (moveDot (iclosure g s) h)` by 
               (SRW_TAC [] [] THEN
		FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, md_append, moveDot] THEN
		METIS_TAC []) THEN
	       Cases_on `moveDot (iclosure g s) h` THEN
	       SRW_TAC [] [] 
               THENL[
		     METIS_TAC [MEM, MEM_APPEND],

		     `∃s'.(trans g (iclosure g (h'::t),vp2) = SOME s') ∧
									    MEM (item nt' (r1 ++ [h] ++ vp2,[NTS nt]++sfx)) s'` 
			 by METIS_TAC [transExists, iclosure_mem, APPEND_ASSOC] THEN
		     FULL_SIMP_TAC (srw_ss()) []
		     ],
	    
	    `MEM (item nt ([],rhs)) s'` by METIS_TAC [transOutMem, APPEND] THEN
	    IMP_RES_TAC transSeqIcGen THEN
	    METIS_TAC [mem_in]
	    ]]);
      


val lemma =store_thm("lemma",
  ``∀n pfx sfx nt rhs. 
      NRC (rderives ag) n [NTS (startSym ag)] 
                          (pfx ++ [NTS nt] ++ sfx) ∧
      MEM (rule nt rhs) (rules ag) ⇒
      ∃s. (trans ag (initItems ag (rules ag), pfx) = SOME s) ∧
          MEM (item nt ([], rhs)) s``,
  completeInduct_on `n` THEN 
  `(n = 0) ∨ ∃m. n = SUC m` by METIS_TAC [num_CASES] 
   THENL [
	  SRW_TAC [][] THEN 
	  FULL_SIMP_TAC (srw_ss()) [lreseq] THEN 
	  SRW_TAC [][trans] THEN METIS_TAC [memInitProds],

    SRW_TAC [][] THEN 
    FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
    SRW_TAC [] [] THEN 
    `0 < SUC m` by DECIDE_TAC THEN
    `∃m1 m2 pfx1 pfx2 sfx1 sfx2 sfx2' nt'.
           m1 < (SUC m) ∧ m2 < (SUC m) ∧
           NRC (rderives ag) m1 [NTS (startSym ag)]
             (pfx1 ++ [NTS nt'] ++ sfx1) ∧
           MEM (rule nt' (pfx2 ++ [NTS nt] ++ sfx2)) (rules ag) ∧
           NRC (rderives ag) m2
             (pfx1 ++ pfx2 ++ [NTS nt] ++ sfx2 ++ sfx1)
             (pfx1 ++ pfx2 ++ [NTS nt] ++ sfx2' ++ sfx1) ∧
           (pfx = pfx1 ++ pfx2) ∧ (sfx = sfx2' ++ sfx1)` 
	by METIS_TAC [sublemma] THEN
    SRW_TAC [] [] THEN
    `∃s.(trans ag (initItems ag (rules ag),pfx1) =
         SOME s) ∧ 
         MEM (item nt' ([],(pfx2 ++ [NTS nt] ++ sfx2))) s` 
	by METIS_TAC [] THEN
    METIS_TAC [transShiftExists, initItems]
    ]);
 


val transOutEq = store_thm ("transOutEq",
``∀s0 pfx s s'.
  (trans g (s0,pfx) = SOME s) ⇒
  (trans g (s0,pfx) = SOME s') ⇒
  (s=s')``,
Induct_on `pfx` THEN SRW_TAC [] [trans]);
    



val doReduce = Define 
`doReduce m ((sym::rst), os, ((s, itl)::rem)) ru =
                   if (isNonTmnlSym sym) then NONE 
                   else 
                       let 
                           l = ruleLhs ru and
                           r = ruleRhs ru 
                       in 
                           let 
                                 ptree = addRule os ru 
                           in 
                                case ptree of NONE -> NONE 
                                || (SOME p) -> 
                                   let 
                                       newStk = pop os (LENGTH r) 
                                    in 
					let 
					newStateStk = pop  ((s, itl)::rem) (LENGTH r)
					in
					if (newStateStk = []) then NONE else
					let 
                                            topitl = SND (HD newStateStk)
					in
					    let
						nx = ((FST m) topitl (NTS l))
					    in
						if (nx=[]) then NONE else
						let 
						    ns = ((NTS l), nx)
						in 
						    SOME ((sym::rst),([(ns,p)] ++ newStk), push newStateStk ns)`;


(*!!!!Make this followSetML*)
val red_eq1 = store_thm ("red_eq1",
``~(TS sym IN followSet g (NTS s)) ⇒
(reduce g itl sym = reduce g (item s (q,[])::itl) sym)``,

SRW_TAC [] [reduce]);

(*!!!!Make this followSetML*)
val red_eq2 = store_thm ("red_eq2",
``(TS sym IN followSet g (NTS s)) ⇒
((rule s q::reduce g itl sym) = reduce g (item s (q,[])::itl) sym)``,
SRW_TAC [] [reduce]);


(*!!!!Make this followSetML*)
val reduce_mem = store_thm ("reduce_mem", 
``∀sym itl out.(reduce g itl sym = out) ⇒ 
(∀e.MEM e out ⇒ ∃l r1.(e=rule l r1) ∧ (MEM (item l (r1,[])) itl))``,

Induct_on `itl` THEN SRW_TAC [] [] THEN1
(Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [reduce]) THEN
Cases_on `h` THEN Cases_on `p` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce, LET_THM, option_case_rwt, 
 list_case_rwt, pairTheory.FORALL_PROD] 
THENL[

 Cases_on `(TS sym) IN (followSet g (NTS n))` THENL[
 `MEM e ((rule n q)::reduce g itl sym)` by METIS_TAC [red_eq2] THEN
 `(e=rule n q) ∨ (MEM e (reduce g itl sym))` by METIS_TAC [MEM] THENL[
 Cases_on `e` THEN
 METIS_TAC [reduce, red_eq1],
 METIS_TAC [MEM]],
 METIS_TAC [MEM , reduce]],

 METIS_TAC [MEM , reduce]]);



val getstate_red = store_thm ("getstate_red", 
``∀m itl sym g.(m = (sgoto g, reduce g)) ⇒
validItl g itl ⇒ (getState m itl sym = REDUCE r) ⇒ MEM r (rules g)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState, LET_THM] THEN
Cases_on `sgoto g itl sym` THEN 
Cases_on `reduce g itl (ts2str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[
 Cases_on `~(LENGTH t = 0)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `sym` THEN Induct_on `itl` THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [reduce] THEN `t=[]` by METIS_TAC [LENGTH_NIL] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
 `∀e.MEM e [h] ⇒
 ∃l r1. (e = rule l r1) ∧ MEM (item l (r1,[])) (h'::itl)` by METIS_TAC [reduce_mem] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_mem,validItl, THE_DEF, APPEND, CONS, EVERY_DEF] THEN
`validItl g [h']` by METIS_TAC [APPEND, validItl_append] THEN
METIS_TAC [reduce_mem,validItl, APPEND, CONS, EVERY_DEF, MEM, validItl_append, rgr_r9eq, 
 APPEND_NIL],

Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`∀e.MEM e (h'::t') ⇒
         ∃l r1. (e = rule l r1) ∧ MEM (item l (r1,[])) itl` by METIS_TAC [reduce_mem]
THEN
FULL_SIMP_TAC (srw_ss()) [reduce_mem,validItl, THE_DEF, APPEND, CONS, EVERY_DEF] THEN
METIS_TAC [reduce_mem,validItl, APPEND, CONS, EVERY_DEF, MEM, validItl_append, rgr_r9eq, 
APPEND_NIL]]);


val getState_mem_itl = store_thm ("getState_mem_itl", 
``validItl g itl ⇒ (m = (sgoto g, reduce g)) ⇒ isTmnlSym e ⇒
(getState m itl e = REDUCE (rule s' l)) ⇒ (MEM (item s' (l,[])) itl)``,

SRW_TAC [] [] THEN
`MEM (rule s' l) (rules g)` by METIS_TAC [getstate_red] THEN
FULL_SIMP_TAC (srw_ss()) [getState, LET_THM] THEN
Cases_on `sgoto g itl e` THEN Cases_on `reduce g itl (ts2str e)` THEN 
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]  THENL[
Cases_on `LENGTH t = 0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`MEM (rule s' l) (rule s' l::t)` by METIS_TAC [MEM] THEN
`∃l' r1. (rule s' l = rule l' r1) ∧ MEM (item l' (r1,[])) itl` by METIS_TAC [reduce_mem] THEN
FULL_SIMP_TAC (srw_ss()) [],

Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`MEM (rule s' l) (rule s' l::t')` by METIS_TAC [MEM] THEN
`∃l' r1. (rule s' l = rule l' r1) ∧ MEM (item l' (r1,[])) itl` by METIS_TAC [reduce_mem] THEN
FULL_SIMP_TAC (srw_ss()) []]);


val validItl_initProds2Items = store_thm ("validItl_initProds2Items", 
``∀g l.validItl g (initProds2Items sym (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initProds2Items, validItl, rules_def] THEN
Cases_on `h` THEN
SRW_TAC [] [initProds2Items, validItl, rules_def] THEN
METIS_TAC [validItl_rules_cons]);



val parse = Define `
(parse m (inp, os, ((s, itl)::rem)) = 
	case inp of [] -> NONE
	    || [e] -> 
	    (let      
		 newState = getState m itl e
	     in 
		 case newState of NA -> NONE 
		   || (GOTO st) -> NONE		     
		   || (REDUCE ru) -> doReduce m ([e], os, ((s, itl)::rem)) ru)

	    || (sym::rst) -> 
		 (let      
		     newState = getState m itl sym 
		 in 
		     case newState of NA -> NONE 
		       || (GOTO st) -> 
			 if (isNonTmnlSym sym) then NONE 
			 else (* shift goto *) 
			     SOME (rst,((sym,st),Leaf (ts2str sym))::os, push ((s, itl)::rem) (sym,st))
			   || (REDUCE ru) -> doReduce m ((sym::rst), os, ((s, itl)::rem)) ru))`;
    


(* parser :: machine -> symbol list -> ((state,ptree) list -> ptree option *)
val stackSyms = Define `stackSyms stl = (REVERSE (MAP FST (MAP FST stl)))`;

val exitCond = Define 
`exitCond (eof,oldSym)  (inp,stl,csl) =  
    (~(stl=([]:((('nts,'ts)symbol # ('nts,'ts)state) # ('nts,'ts)ptree) list)) ∧ 
     (stackSyms stl = [oldSym]) ∧ 
     (inp = [TS eof]))`;

val init = Define
`init inis sl =  
(sl,([]:((('nts,'ts)symbol# ('nts,'ts)state) # ('nts,'ts)ptree) list),[inis])`;

val parser = Define `parser (initConf, eof, oldS) m sl = 
let 
out = (mwhile (\s. ~(exitCond (eof,NTS oldS) s))
(\(sli,stli,csli).parse m (sli,stli, csli)) (sl,([]:((('nts,'ts)symbol# ('nts,'ts)state) # ('nts,'ts)ptree) list),[initConf]))
in
    case out of NONE -> NONE
              || (SOME (SOME (slo,[(st1,pt)],cs))) -> SOME (SOME pt)
	     || SOME (NONE) -> SOME (NONE)
	|| SOME _ -> SOME NONE`;



(* yacc :: grammar -> symbol list -> ptree opion*)
val lrparse = Define `lrparse g s' eof sl = 
let 
    g' = auggr g s' eof
in
    case g' of NONE -> NONE
    || (SOME ag) ->
       (let
	    mac = slrmac ag (* slrML g [(initItems ag (rules ag))] (SET_TO_LIST (allSyms g))  -- FOR ML version*)
	in 
	    case mac of NONE -> NONE
            || (SOME m) -> (
      let
	  initConf =  ((NTS s'), initItems ag (rules ag))
      in
	  case (parser (initConf,eof,startSym g) m sl) 
	   of NONE -> NONE
		|| SOME (NONE) -> NONE
		|| SOME (SOME out) -> SOME out))`;



val parseExp = store_thm
("parseExp",
``∀Q.(\(x,y,z).parse Q (x,y,z)) = parse Q``,
SRW_TAC [] [FUN_EQ_THM,UNCURRY]);


val mlDir = ref ("./theoryML/");

(*
val list_size_def =
  REWRITE_RULE [arithmeticTheory.ADD_ASSOC]
               (#2 (TypeBase.size_of ``:'a list``));*)

(*
val _ =
 let open EmitML
 in emitML (!mlDir)
   ("yacc",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree","firstSet", "followSet", "parser"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: MLSIG "type item = parserML.item"
    :: MLSIG "type state = parserML.state"
    :: DATATYPE `action = REDUCE of rule | GOTO of state | NA`
    :: DEFN getItems
    :: DEFN iclosure1
    :: DEFN iclosure
    :: DEFN auggr
    :: DEFN initProds2Items
    :: DEFN initItems
    :: DEFN moveDot
    :: DEFN nextState
    :: DEFN sgoto
    :: DEFN reduce
    :: DEFN buildTree
    :: DEFN addRule
    :: DEFN machine
    :: DEFN findItemInRules
    :: DEFN itemEqRuleList
    :: DEFN getState
    :: DEFN doReduce
    :: DEFN parse
    :: DEFN parser
    :: [])
 end;

*)
(*
Theorems
1. ∃g.~(yacc g = NONE)

2. s IN language (g) ∧ (yacc (g) = SOME lrm) ⇒ ∃t.(parse lrm s = SOME (t))

3. (yacc g = SOME lrm) ⇒ unambiguous (g)

4. (yacc g sl = SOME tree) ⇒ (validptree tree g ∧ (leaves tree = sl))

*)

val _ = export_theory();
