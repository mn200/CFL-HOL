open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
whileLemmasTheory parseTreeTheory parserDefTheory yaccDefTheory
parseProp1DefTheory parseProp2DefTheory

val _ = new_theory "parserPropDefTheory"

val prop1Ext = Define `prop1Ext g stl csl = prop1 g stl /\ ~NULL csl /\ validStates g csl`


val parserProp1thm = store_thm ("parserProp1thm",
``!g sl stl.(auggr g s eof = SOME ag) ==>
(slr ag = m) ==> prop1Ext ag stl csl ==>
(parser ag m sl [] csl (TS eof) (NTS (startSym g)) = SOME (SOME tree))
==> validptree ag tree``,

SRW_TAC [] [parser_def, prop1Ext] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM, Abbrev_def] THEN
Cases_on `               mwhile (\(sli,stli,csli).
                  ~(sli = [TS eof]) \/
                  ~(stateSym (FST (HD stli)) = NTS (startSym g)))
               (\(sli,stli,csli). parse (slr ag) (sli,stli,csli))
               (SOME (sl,[],csl))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM MP_TAC THEN
Q.MATCH_ABBREV_TAC `(mwhile CC ff (SOME ss) = SOME (SOME ss')) ==>
validptree ag tree` THEN
STRIP_TAC THEN
SRW_TAC [] [] THEN
`~ CC ss'` by METIS_TAC [mwhileEndCond, SOME_11] THEN
Q.ABBREV_TAC 
`PP = \(sli,stli,csli) : symbol list # (state # ptree) list # state list.
prop1 ag stli /\
validStates ag csli /\
~ NULL csli` THEN

Q_TAC SUFF_TAC `PP ss'` THENL[
Q.UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [prop1_def, stacklsymtree_def] THEN 
Cases_on `q'` THEN
FULL_SIMP_TAC (srw_ss()) [stateSym_def, validStkSymTree_def] THEN
`validptree ag r` by METIS_TAC [isNonTmnlSym_def, MEM, stacklsymtree_def] THEN
FULL_SIMP_TAC (srw_ss()) [validptree, getSymbols_def, getSymsEqptree2Sym,
ptree2Sym_def, tmnlSym_def, tmnlToStr_def] THEN
SRW_TAC [] [nonTmnlToStr_def] THEN
METIS_TAC [ag_new_rule, isNode_def, isNonTmnlSym_def],

MATCH_MP_TAC (GEN_ALL mwhileEndState) THEN
MAP_EVERY Q.EXISTS_TAC [`ss`, `ff`, `CC`] THEN
SRW_TAC [][] THENL [

(* PP is a loop invariant *)
Q.UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
`?sli0 stli0 csli0. x = (sli0,stli0,csli0)`
by METIS_TAC [pairTheory.pair_CASES] THEN
`?sli stli csli. x' = (sli,stli,csli)`
by METIS_TAC [pairTheory.pair_CASES] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
(* prop1 preserved*)
`?sitl rest. csli0 = sitl :: rest`
by (Cases_on `csli0` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`?nt itl. sitl = state nt itl`
by (Cases_on `sitl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`validItl ag itl` by FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
METIS_TAC [prop1thm, parse_csl_validStates, parse_csl_not_nil],

(* PP holds initially *)
Q.UNABBREV_ALL_TAC THEN SRW_TAC [][prop1_def, validStkSymTree_def, validptree] THEN
METIS_TAC [MEM, stacklsymtree_def]]])



val parserProp2thm = store_thm ("parserProp2thm",
``!m g s eof sl csl.(auggr g s eof = SOME ag) ==>  ~NULL csl ==> validStates ag csl ==>
(m=slr ag) ==> prop2 sl sl [] ==> 
(parser ag m sl [] csl (TS eof) (NTS (startSym g)) = SOME (SOME tree)) ==>
(sl=leaves tree)``,

SRW_TAC [] [parser_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM, Abbrev_def] THEN
Cases_on `mwhile
               (\(sli,stli,csli).
                  ~(sli = [TS eof]) \/
                  ~(stateSym (FST (HD stli)) = NTS (startSym g)))
               (\(sli,stli,csli). parse (slr ag) (sli,stli,csli))
               (SOME (sl,[],csl))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM MP_TAC THEN
Q.MATCH_ABBREV_TAC `(mwhile CC ff (SOME ss) = SOME (SOME ss')) ==>
(sl=leaves tree)` THEN
STRIP_TAC THEN
SRW_TAC [] [] THEN
`~ CC ss'` by METIS_TAC [mwhileEndCond, SOME_11] THEN
Q.ABBREV_TAC 
`PP = \(sli,stli,csli) : symbol list # (state # ptree) list # state list.
prop2 sl sli (REVERSE stli) /\ ~NULL csli /\ validStates ag csli` THEN

Q_TAC SUFF_TAC `PP ss'` THENL[
Q.UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [prop2_def, leaves_def] THEN 
Cases_on `q'` THEN
FULL_SIMP_TAC (srw_ss()) [stacktreeleaves_def] THEN
METIS_TAC [tmnlSym_def, tmnlToStr_def],


MATCH_MP_TAC (GEN_ALL mwhileEndState) THEN
MAP_EVERY Q.EXISTS_TAC [`ss`, `ff`, `CC`] THEN
SRW_TAC [][] THENL [

(* PP is a loop invariant *)
Q.UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
`?sli0 stli0 csli0. x = (sli0,stli0,csli0)`
by METIS_TAC [pairTheory.pair_CASES] THEN
`?sli stli csli. x' = (sli,stli,csli)`
by METIS_TAC [pairTheory.pair_CASES] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN

(* prop2 preserved*)
`?sitl rest. csli0 = sitl :: rest`
by (Cases_on `csli0` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`?nt itl. sitl = state nt itl`
by (Cases_on `sitl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`validItl ag itl` by FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
METIS_TAC [parse_csl_validStates,prop2thm, parse_csl_not_nil, NOT_CONS_NIL, prop2_def, validStates_def],

(* PP holds initially *)
Q.UNABBREV_ALL_TAC THEN SRW_TAC [][prop2_def, leaves_def, stacktreeleaves_def]]])


val lem1 = store_thm ("lem1",
``(!t.
            MEM t ptl /\ isNode t ==>
            RTC (derives g) [ptree2Sym t] (leaves t)) ==> RTC (derives g) (MAP ptree2Sym ptl) (cleaves ptl)``,
Induct_on `ptl` THEN  SRW_TAC [] [ptree2Sym_def, leaves_def, RTC_RULES] THEN
Cases_on `h` THEN SRW_TAC [] [ptree2Sym_def, leaves_def] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [isNode_def, ptree2Sym_def, leaves_def] THENL[
`RTC (derives g) [(TS (tmnlToStr t))] [(TS (tmnlToStr t))]` by METIS_TAC [RTC_RULES] THEN
METIS_TAC [derives_append, APPEND],
METIS_TAC [derives_append, APPEND]])



val vpt_rtcd = store_thm ("vpt_rtcd",
``!g t.validptree g t ==> RTC (derives g) [ptree2Sym t] (leaves t)``,
HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
`derives g [NTS (nonTmnlToStr n)] (MAP ptree2Sym ptl)` by METIS_TAC [res1, getSymsEqptree2Sym] THEN
Q_TAC SUFF_TAC `RTC (derives g) (MAP ptree2Sym ptl) (leaves (Node n ptl))` THENL[
SRW_TAC [] [ptree2Sym_def] THEN METIS_TAC [RTC_RULES, getSymsEqptree2Sym],
METIS_TAC [lem1, leaves_def]])




val _ = export_theory ();


