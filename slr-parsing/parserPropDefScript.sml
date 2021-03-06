open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
whileLemmasTheory parseTreeTheory yaccDefTheory

open parseProp1DefTheory

open parseProp2DefTheory

val _ = new_theory "parserPropDef"

Definition parser_inv_def:
  parser_inv g stl csl ⇔ validptree_inv g stl /\
                         ~NULL csl /\ validStates g csl
End

val parser_inv = parser_inv_def


val parserValidptree_Invthm = store_thm ("parserValidptree_Invthm",
``∀g sl stl.(auggr g s eof = SOME ag) ==>
(slrmac ag = SOME m) ==> parser_inv ag stl csl ==>
(parser ((NTS (startSym ag),initItems ag (rules ag)),
         eof, startSym g) m sl = SOME (SOME tree)) ==>
validptree ag tree``,

SRW_TAC [] [parser_def, parser_inv,init_def] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM, Abbrev_def] THEN
Q.ABBREV_TAC `inis = (NTS (startSym ag),initItems ag (rules ag))` THEN
Cases_on `mwhile (λs. ¬exitCond (eof,NTS (startSym g)) s)
           (λ(sli,stli,csli). parse m (sli,stli,csli))
           (sl,[],[(NTS (startSym ag),initItems ag (rules ag))])` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM MP_TAC THEN
Q.MATCH_ABBREV_TAC `(mwhile CC ff ss = SOME (SOME ss')) ==>
validptree ag tree` THEN
STRIP_TAC THEN
SRW_TAC [] [] THEN
`~ CC ss'` by METIS_TAC [mwhileEndCond, SOME_11] THEN
Q.ABBREV_TAC
`PP = \(sli,stli,csli) :
((α,β) symbol list # ((((α,β) symbol # (α,β)state) # (α,β) ptree) list) #
(((α,β) symbol# (α,β) state) list)).
validptree_inv ag stli ∧
validStates ag csli ∧
¬ NULL csli` THEN

Q_TAC SUFF_TAC `PP ss'` THENL[
UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validptree_inv_def, stacklsymtree_def] THEN
Cases_on `q'` THEN
FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree_def,exitCond_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

MATCH_MP_TAC (GEN_ALL mwhileEndState) THEN
MAP_EVERY Q.EXISTS_TAC [`ss`, `ff`, `CC`] THEN
SRW_TAC [][] THENL [

(* PP is a loop invariant *)
UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
`?sli0 stli0 csli0. x = (sli0,stli0,csli0)`
by METIS_TAC [pairTheory.pair_CASES] THEN
`?sli stli csli. x' = (sli,stli,csli)`
by METIS_TAC [pairTheory.pair_CASES] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
(* validptree_inv preserved*)
`?sitl rest. csli0 = sitl :: rest`
by (Cases_on `csli0` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`?nt itl. sitl = (nt, itl)`
by (Cases_on `sitl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`validItl ag itl` by FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
METIS_TAC [validptree_invthm, parse_csl_validStates, parse_csl_not_nil],

(* PP holds initially *)
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
SRW_TAC [][] THEN
SRW_TAC [][validptree_inv_def, validStkSymTree_def, validptree,init_def] THEN
FULL_SIMP_TAC (srw_ss()) [validStates_def, initItems_def] THEN
METIS_TAC [validItl_initProds2Items, validItl_iclosure,MEM,
	   stacklsymtree_def]
]]);


val soundness = store_thm ("soundness",
``∀g sl stl.(auggr g s eof = SOME ag) ∧
(slrmac ag = SOME m) ∧ parser_inv ag stl csl ∧
(parser ((NTS (startSym ag),initItems ag (rules ag)),
         eof, startSym g) m sl = SOME (SOME tree)) ⇒
sl ∈ language ag``,

cheat);

(*
SRW_TAC [][language_def] THEN
`validptree ag tree` by METIS_TAC [parserValidptree_Invthm] THEN
Cases_on `tree` THEN
FULL_SIMP_TAC (srw_ss()) [validptree, parser_def, LET_THM] THEN
Cases_on `mwhile (λs. ¬exitCond (eof,NTS (startSym g)) s)
           (λ(sli,stli,csli). parse m (sli,stli,csli))
           (init (NTS (startSym ag),initItems ag (rules ag)) sl)` THEN
FULL_SIMP_TAC (srw_ss()) [init_def] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM MP_TAC THEN
Q.MATCH_ABBREV_TAC `(mwhile CC ff ss = SOME (SOME ss')) ==>
(derives ag)^* [NTS (startSym ag)] sl` THEN
STRIP_TAC THEN
SRW_TAC [] [] THEN
`~ CC ss'` by METIS_TAC [mwhileEndCond, SOME_11] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [exitCond_def, stackSyms_def] THEN
SRW_TAC [][] THEN
cheat);
*)

val parse_sl_not_nil = store_thm ("parse_sl_not_nil",
``!m g.(SOME m=slrmac g) ==>
 ~(sl=[]) ==>
 ((parse m (sl, stl, ((s, itl)::csl)) = SOME (sl',stl',csl'))) ==>
  ~(sl'=[])``,

SRW_TAC [] [parse_def, LET_THM] THEN
Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN
Cases_on `getState m itl h` THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      METIS_TAC [red_sym, NOT_CONS_NIL, APPEND],

      METIS_TAC [red_sym, NOT_CONS_NIL, APPEND],

      Cases_on `isNonTmnlSym h` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [NOT_CONS_NIL]
      ]
);



val parserLeaves_Eq_Invthm = store_thm
("parserLeaves_Eq_Invthm",
 ``∀m (g:(α,β) grammar) (s:α) (eof:β) sl csl.
 (auggr g s eof = SOME ag) ==>
  ~NULL csl ==> validStates ag csl ==>
(slrmac ag = SOME m) ==>
(inis = (NTS (startSym ag), initItems ag (rules ag))) ==>
(parser (inis, eof, startSym g) m sl = SOME (SOME tree)) ==>
(sl=MAP TS (leaves tree) ++ [TS eof])``,

SRW_TAC [] [parser_def, LET_THM] THEN
`leaves_eq_inv sl sl ([]: ((γ # δ) # (α, β) ptree) list)`
 by SRW_TAC [][leaves_eq_inv_def, stacktreeleaves_def] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM, Abbrev_def] THEN
Q.ABBREV_TAC `inis = (NTS (startSym ag), initItems ag (rules ag))` THEN
Cases_on `mwhile (λs. ¬exitCond (eof,NTS (startSym g)) s)
           (λ(sli,stli,csli). parse m (sli,stli,csli))
           (init (NTS (startSym ag),initItems ag (rules ag)) sl)` THEN
FULL_SIMP_TAC (srw_ss()) [init_def] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM MP_TAC THEN
Q.MATCH_ABBREV_TAC `(mwhile CC ff ss = SOME (SOME ss')) ==>
(sl=MAP TS (leaves tree) ++ [TS eof])` THEN
STRIP_TAC THEN
SRW_TAC [] [] THEN
`~ CC ss'` by METIS_TAC [mwhileEndCond, SOME_11] THEN
Q.ABBREV_TAC
`PP = \(sli,stli,csli) :
((α,β) symbol list # ((((α,β) symbol # (α,β) state) # (α,β)ptree) list) #
(((α,β)symbol#(α,β)state) list)).
leaves_eq_inv sl sli (REVERSE stli) /\
validStates ag csli /\ ~NULL csli` THEN
Q_TAC SUFF_TAC `PP ss'`
THENL[
UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [leaves_eq_inv_def, leaves_def,
			  exitCond_def,init_def] THEN
Cases_on `q'` THEN
Cases_on `q''` THEN
FULL_SIMP_TAC (srw_ss()) [stacktreeleaves_def,stackSyms_def] THEN
SRW_TAC [][] THEN
Cases_on `q` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [tmnlSym_def],


MATCH_MP_TAC (GEN_ALL mwhileEndState) THEN
MAP_EVERY Q.EXISTS_TAC [`ss`, `ff`, `CC`] THEN
SRW_TAC [][] THENL [

(* PP is a loop invariant *)
UNABBREV_ALL_TAC THEN SRW_TAC [][] THEN
`?sli0 stli0 csli0. x = (sli0,stli0,csli0)`
by METIS_TAC [pairTheory.pair_CASES] THEN
`?sli stli csli. x' = (sli,stli,csli)`
by METIS_TAC [pairTheory.pair_CASES] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
(* leaves_eq_inv preserved*)
`?sitl rest. csli0 = sitl :: rest`
by (Cases_on `csli0` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`?nt itl. sitl = (nt, itl)`
by (Cases_on `sitl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
SRW_TAC [][] THEN
`validItl ag itl` by FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
METIS_TAC [parse_csl_validStates,leaves_eq_invthm, parse_csl_not_nil, NOT_CONS_NIL, leaves_eq_inv_def, validStates_def],

(* PP holds initially *)
UNABBREV_ALL_TAC THEN
SRW_TAC [][leaves_eq_inv_def, leaves_def, stacktreeleaves_def,init_def] THEN
FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
SRW_TAC [][leaves_eq_inv_def, leaves_def, stacktreeleaves_def] THEN
FULL_SIMP_TAC (srw_ss()) [validStates_def, initItems_def] THEN
METIS_TAC [validItl_initProds2Items, validItl_iclosure]
]]);


val _ = export_theory ();
