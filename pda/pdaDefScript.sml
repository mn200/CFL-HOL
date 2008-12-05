open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory

open listLemmasTheory containerLemmasTheory relationLemmasTheory


val _ = new_theory "pdaDef"

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val SUBSET_FINITE' = 
    SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO]
	      SUBSET_FINITE;


(* to change to list approach, replace next -> with #, and put
   list onto end of next field's type. *)

val _ = type_abbrev ("trans", 
              ``:('isym option # 'ssym # 'state) #
                 ('state # 'ssym list )``);


val _ = Hol_datatype 
`pda = <| start:'state ;      
          ssSym:'ssym ;          
	  next: ('isym,'ssym,'state) trans list; 
	  final:'state list |>`;



val inpSyms = Define
`inpSyms p = 
    { isym:'isym | ?out q ssym. 
             MEM ((SOME isym,ssym,q),out) p.next}`;


val inpSymsList = Define
`(inpSymsList [] = []) ∧
 (inpSymsList (((SOME isym:'isym option,ssym,q),out)::rst) = 
                                isym::inpSymsList rst) ∧
 (inpSymsList (((NONE,ssym,q),out)::rst) = inpSymsList rst)`;

val _ = export_rewrites ["inpSymsList_def"];

val FORALL_trans = store_thm(
  "FORALL_trans",
  ``!P. (!t. P (t: ('is,'ss,'st) trans)) = 
        (!isopt ss st st' syms. P ((isopt, ss, st),(st', syms)))``,
  SRW_TAC [][EQ_IMP_THM] THEN 
  `?a b c d e. t = ((a,b,c),(d,e))`
     by METIS_TAC [TypeBase.nchotomy_of ``:'a#'b``] THEN 
  SRW_TAC [][]);

val EXISTS_trans = store_thm(
  "EXISTS_trans",
  ``!P. (?t. P (t : ('is,'ss,'st) trans)) = 
        (?isopt ss st st' syms. P ((isopt,ss,st), (st', syms)))``,
  GEN_TAC THEN MP_TAC (AP_TERM ``$~`` 
			       (Q.SPEC `$~ o P` FORALL_trans)) THEN
  SIMP_TAC pure_ss [NOT_FORALL_THM] THEN 
  SRW_TAC [][]);

val inpSyms_list_eqresult = store_thm(
  "inpSyms_list_eqresult",
  ``inpSyms p = set (inpSymsList p.next)``,
  SRW_TAC [][inpSyms, EXTENSION] THEN 
  Q.SPEC_TAC (`p.next`, `l`) THEN 
  Induct THEN 
  ASM_SIMP_TAC (srw_ss()) [FORALL_trans, EXISTS_OR_THM, 
			   optionTheory.FORALL_OPTION]);
 


val stkSyms = Define
`stkSyms p = {p.ssSym:'ssym} UNION
             { ssym | ?out isym q. 
                      MEM ((isym,ssym,q),out) p.next }
	     UNION
             (BIGUNION
             { set ssyms | ?isym ssym q q'. 
                       MEM ((isym,ssym,q),(q',ssyms)) p.next })`;

val stkSymsList' = Define
`(stkSymsList' [] = []) ∧
 (stkSymsList' (((isym,ssym,q),(q',ssyms))::rst) =
                     ssym::ssyms ++ stkSymsList' rst)`;

val stkSymsList = Define
`(stkSymsList p l = [p.ssSym:'ssym] ++ stkSymsList' l)`;


val ssymslApp = store_thm
("ssymslApp",
``∀l1 l2.stkSymsList' (l1++l2) = 
            stkSymsList' l1 ++ stkSymsList' l2``,
Induct_on `l1` THEN Induct_on `l2` THEN
SRW_TAC [][stkSymsList'] THEN
Cases_on `h'` THEN Cases_on `r` THEN
Cases_on `q` THEN Cases_on `r` THEN
SIMP_TAC (srw_ss()) [stkSymsList'] THEN
METIS_TAC [APPEND, APPEND_ASSOC]);


val memssl' = store_thm
("memssl'",
``∀l.MEM ssym (stkSymsList' l)
        ⇒
    ∃isym q q' ssyms.MEM ((isym,ssym,q),q',ssyms)l ∨
    ∃isym q q' x ssyms.MEM ((isym,x,q),q',ssyms)l ∧
                       MEM ssym ssyms``,
Induct_on `l` THEN SRW_TAC [][stkSymsList'] THEN
Cases_on `h` THEN Cases_on `r` THEN
Cases_on `q` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [stkSymsList'] THEN
METIS_TAC []);

val stkSyms_list_eqresult = store_thm(
  "stkSyms_list_eqresult",
  ``stkSyms p = set (stkSymsList p p.next)``,

  SRW_TAC [][stkSyms, EXTENSION, EQ_IMP_THM, stkSymsList] 
  THENL[
	FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ssymslApp] THEN
	Cases_on `out` THEN
	SRW_TAC [][stkSymsList'] THEN
	METIS_TAC [APPEND, APPEND_ASSOC],

	FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ssymslApp] THEN
	SRW_TAC [][stkSymsList'] THEN
	METIS_TAC [APPEND, APPEND_ASSOC],

	IMP_RES_TAC memssl' THEN1
	METIS_TAC [] THEN
	DISJ2_TAC THEN
	Q.EXISTS_TAC `set ssyms'` THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	METIS_TAC [mem_in]
	]);
 

val states = Define
`states p = {p.start:'state} UNION set p.final UNION
             { q | ?out isym ssym. 
                      MEM ((isym,ssym,q),out) p.next }
	     UNION
             { q' | ?isym ssym q ssyms. 
                       MEM ((isym,ssym,q),(q',ssyms)) p.next }`;

val statesList' = Define
`(statesList' [] = []) ∧
 (statesList' (((isym,ssym,q),(q',ssyms))::rst) = 
                    q::q'::statesList' rst)`;

val statesList = Define
`statesList p d = p.start:'state::p.final ++ statesList' d`;

val memstl' = store_thm
("memstl'",
``∀l.MEM q (statesList' l)
        ⇒
    ∃isym ssym q' ssyms.MEM ((isym,ssym,q),q',ssyms)l ∨
    ∃isym ssym q' ssyms.MEM ((isym,ssym,q'),q,ssyms)l``,
Induct_on `l` THEN SRW_TAC [][statesList'] THEN
Cases_on `h` THEN Cases_on `r` THEN
Cases_on `q'` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [statesList'] THEN
METIS_TAC []);

val states_list_eqresult = store_thm(
  "states_list_eqresult",
  ``states p = set (statesList p p.next)``,
  SRW_TAC [][states, EXTENSION, EQ_IMP_THM, statesList] 
  THENL[
	METIS_TAC [],

 	FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	Cases_on `out` THEN
	SRW_TAC [][statesList', statesListApp] THEN
	METIS_TAC [APPEND, APPEND_ASSOC],

 	FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	SRW_TAC [][statesList', statesListApp] THEN
	METIS_TAC [APPEND, APPEND_ASSOC],
	
	METIS_TAC [],
	
	METIS_TAC [memstl']]);



val finiteInpSyms = store_thm
("finiteInpSyms",
``!p. FINITE (inpSyms p)``,
SRW_TAC [][inpSyms_list_eqresult]);

val finiteStkSyms = store_thm
("finiteStkSyms",
``!p. FINITE (stkSyms p)``,
  SRW_TAC [][stkSyms] THENL [
    Q.MATCH_ABBREV_TAC `FINITE ss` THEN 
    Q_TAC SUFF_TAC 
	  `ss = set (MAP (FST o SND o FST) p.next)` 
	  THEN1 SRW_TAC [][] THEN 
    UNABBREV_ALL_TAC THEN 
    SIMP_TAC (srw_ss()) [EXTENSION, MEM_MAP, EXISTS_trans, 
			 pairTheory.EXISTS_PROD] THEN 
    METIS_TAC [],

    Q.MATCH_ABBREV_TAC `FINITE ss` THEN 
    Q_TAC SUFF_TAC 
	  `ss = set (MAP set 
			 (MAP (SND o SND) p.next))`
	  THEN1 SRW_TAC [][] THEN 
    UNABBREV_ALL_TAC THEN 
    SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) 
	     [Once EXTENSION, MEM_MAP, EXISTS_trans],

    SRW_TAC [][]
  ]);

    
val finiteStates = store_thm
("finiteStates",
``!p. FINITE (states p)``,
SRW_TAC [][states] THEN
Q.MATCH_ABBREV_TAC `FINITE ss` THENL[ 
Q_TAC SUFF_TAC `ss = set (MAP (SND o SND o FST) p.next)` 
	  THEN1 SRW_TAC [][] THEN 
    UNABBREV_ALL_TAC THEN 
    SIMP_TAC (srw_ss()) [EXTENSION, MEM_MAP, EXISTS_trans, 
			 pairTheory.EXISTS_PROD] THEN 
    METIS_TAC [],

    Q.MATCH_ABBREV_TAC `FINITE ss` THEN 
    Q_TAC SUFF_TAC 
	  `ss = set (MAP (FST o SND) p.next)`
	  THEN1 SRW_TAC [][] THEN 
    UNABBREV_ALL_TAC THEN 
    SIMP_TAC (srw_ss()) [EXTENSION, MEM_MAP, EXISTS_trans, 
			 pairTheory.EXISTS_PROD] THEN 
    METIS_TAC []]);



val ID = Define 
`(ID p (q,_,[]) y = F) /\
 (ID p (q,[],ssym::srst) (q',inp',ssyms') = 
   (inp'= []) ∧ ?sl.MEM ((NONE,ssym,q),(q',sl)) p.next
   ∧ (ssyms' = sl++srst)) ∧
 (ID p (q,inp::irst,ssym::srst) (q',inp',ssyms') = 
   ((inp'= irst) ∧ ?sl.MEM ((SOME inp,ssym,q),(q',sl)) p.next
   ∧ (ssyms' = sl++srst)) ∨
   ((inp'=inp::irst) ∧ ?sl.MEM ((NONE,ssym,q),(q',sl)) p.next
   ∧ (ssyms' = sl++srst)))`;


val _ = add_rule {
   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
   fixity = Infix(NONASSOC, 550),
   paren_style = OnlyIfNecessary,
   pp_elements = [BreakSpace(1,1), TOK "⊢",
		  BreakSpace(1,2),
                  BeginFinalBlock(PP.INCONSISTENT, 2),
                  TM, HardSpace 1, TOK "→", BreakSpace(1,2)],
                  term_name = "ID"};


val IDC = Define `IDC p s1 s2 = RTC (ID p) s1 s2`;


val lafs = Define 
`lafs (p:('isym, 'ssym, 'state) pda) = 
              { w | ?state stack.
                IDC p (p.start,w,[p.ssSym]) (state,[],stack) ∧ 
                MEM state (p.final) }`;

val laes = Define
`laes (p:('isym, 'ssym, 'state) pda) = 
              { w | ?state.
                    IDC p (p.start,w,[p.ssSym]) (state,[],[]) }`;


(*
Equivalence of acceptance by final state and empty stack

Theorem 5.1
If L is L(M2) for some PDA M2, then L is N(M1) for some PDA, M1.
*)


(* 
{ ((NONE,ssym,q),(qe,[])) | MEM q p.final ∧ 
                            ssym IN (x0 INSERT stkSyms p) }
*)
val fst1 = Define
`fst1 ns ssym fs = ((NONE:'isym option,ssym:'ssym,fs:'state),
                     (ns:'state,[]:'ssym list))`;

val finalStateTrans = Define
`(finalStateTrans ns fsl [] = []) ∧
(finalStateTrans ns fsl (s::rst) = MAP (fst1 ns s) fsl ++
                                   finalStateTrans ns fsl rst)`;

(*
{ ((NONE,ssym,qe),(qe,[])) | ssym IN (x0 INSERT stkSyms p) }
*)
 val newStateTrans = Define
`(newStateTrans ns  [] = []) ∧
(newStateTrans ns (s::rst) = 
       ((NONE:'isym option,s:'ssym,ns:'state),(ns,[]:'ssym list))::
                               newStateTrans ns rst)`;


val newm = Define 
`newm (p:('isym, 'ssym, 'state) pda) 
      (q0:'state,x0:'ssym,qe:'state) = 
let d = [((NONE:'isym option,x0,q0),(p.start,p.ssSym::[x0]))] ++
        p.next ++
        finalStateTrans qe p.final (x0::stkSymsList p p.next)  ++
        newStateTrans qe (x0::stkSymsList p p.next)
in
      <| start := q0;  ssSym := x0;  
         next := d; final := ([]:'state list) |>`;
        

val new_ssym_exists = store_thm(
  "new_ssym_exists",
  ``!s : 'ssym set. INFINITE (UNIV : 'ssym set) ⇒ FINITE s 
            ⇒ 
         ?x. ~(x IN s)``,
   METIS_TAC [IN_UNIV, IN_INFINITE_NOT_FINITE]);


val new_state_exists = store_thm(
  "new_state_exists",
  ``!s : 'state set. INFINITE (UNIV : 'state set) ⇒ FINITE s 
             ⇒ 
           ?x. ~(x IN s)``,
  METIS_TAC [IN_UNIV, IN_INFINITE_NOT_FINITE]);

(*
1-step transitions in the old PDA are still
valid in the new PDA.
*)
val idLafsImpLaes = store_thm
("idLafsImpLaes",
``∀x y. (m:('i,'s,'st)pda) ⊢ x → y ∧ 
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) 
      ⇒
    newm m (q0',x0,qe) ⊢ x → y``,

SRW_TAC [][newm, LET_THM] THEN
Cases_on `x` THEN Cases_on `r` THEN
Cases_on `y` THEN Cases_on `r` THEN
Cases_on `q'` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [ID]);


(*
m-step transitions in the old PDA are still
valid in the new PDA.
*)
val idcLafsImpLaes = store_thm
("idcLafsImpLaes",
``∀x y.(ID m)^* x y ⇒
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m)
      ⇒
   (ID (newm m (q0',x0,qe)))^* x y``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q_TAC SUFF_TAC `newm m (q0',x0,qe) ⊢ x → x'` THEN
METIS_TAC [RTC_RULES, idLafsImpLaes]);


(*
Inserting elements below the current
stack does not invalidate a 1-step
transition
*)
val idStackInsert = store_thm
("idStackInsert",
``m ⊢ (q,x,stk) → (q',x',stk')
      ⇒
   ∀l.m ⊢ (q,x,stk++l) → (q',x',stk'++l)``,

SRW_TAC [][] THEN
Cases_on `x` THEN
Cases_on `stk` THEN
FULL_SIMP_TAC (srw_ss()) [ID]);


(*
Inserting elements below the current
stack does not invalidate an m-step
transition
*)
val idcStackInsert = store_thm
("idcStackInsert",
``(ID m)^* (q,x,stk) (q',x',stk')
      ⇒
   ∀l.(ID m)^* (q,x,stk++l) (q',x',stk'++l)``,

Q_TAC SUFF_TAC 
  `!x y. (ID m)^* x y ==> 
         !q s0 stk q' s1 stk'.
            (x = (q,s0,stk)) ∧ (y = (q',s1,stk')) ⇒
            ∀l. (ID m)^* (q,s0,stk++l) (q',s1,stk'++l)` 
  THEN1 METIS_TAC [] THEN 
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN 
SRW_TAC [][] THEN 
METIS_TAC [idStackInsert, TypeBase.nchotomy_of ``:'a # 'b``, 
	   RTC_RULES]);
 


(*
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
   MEM q m.final
      ⇒
   (ID (newm m (q0',x0,qe))) (q,inp,[ss]) (qe,inp,[])``,

Cases_on `inp` THEN
SRW_TAC [] [ID] THEN
*)

val nstApp = store_thm
("nstApp",
``∀p1 p2.newStateTrans ns (p1++p2) = newStateTrans ns p1 ++
                                     newStateTrans ns p2``,
Induct_on `p1` THEN Induct_on `p2` THEN
SRW_TAC [][newStateTrans])



val newmQeRule = store_thm
("newmQeRule",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
   (MEM h (stkSymsList m m.next) ∨ (h=x0))
        ⇒
     MEM ((NONE,h,qe),qe,[]) (newm m (q0',x0,qe)).next``,

  SRW_TAC [][newm, LET_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
  SRW_TAC [][nstApp, newStateTrans] THEN
  METIS_TAC [APPEND])
  


val idNewmQe = store_thm
("idNewmQe",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  (∀e.MEM e (h::stk) ⇒ MEM e (stkSymsList m m.next) ∨ (e=x0))
      ⇒
    newm m (q0',x0,qe) ⊢ (qe,inp,h::stk) → (qe,inp,stk)``,

Cases_on `inp` THEN
SRW_TAC [][ID] THEN
Q.EXISTS_TAC `[]` THEN
SRW_TAC [][] THEN
METIS_TAC [newmQeRule])


val idcNewmPopStkQe = store_thm
("idcNewmPopStkQe",
``∀stk.¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
   MEM q m.final ∧
  ¬(stk=[]) ∧
  (∀e.MEM e stk ⇒ MEM e (stkSymsList m m.next) ∨ (e=x0))
      ⇒
   (ID (newm m (q0',x0,qe)))^* (qe,inp,stk) (qe,inp,[])``,

Induct_on `stk` THEN
SRW_TAC [][Once RTC_CASES1] THEN
Q.EXISTS_TAC `(qe,inp,stk)` THEN
SRW_TAC [][] 
THENL[
   Cases_on `inp` THEN SRW_TAC [][ID] THEN
   METIS_TAC [newmQeRule, MEM, ID, APPEND],

   Cases_on `stk` THEN SRW_TAC [][]
   ]);


val fstApp = store_thm
("fstApp",
``∀p1 p2.finalStateTrans ns fsl (p1++p2) =
           finalStateTrans ns fsl p1 ++
           finalStateTrans ns fsl p2``,

Induct_on `p1` THEN Induct_on `p2` THEN 
SRW_TAC [][finalStateTrans]);


val newmFstRule = store_thm
("newmFstRule",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
   MEM q m.final ∧
  (MEM h (stkSymsList m m.next) ∨ (h=x0)) 
       ⇒
     newm m (q0',x0,qe) ⊢ (q,inp,h::t) → (qe,inp,t)``,

Cases_on `inp` THEN
SRW_TAC [][newm, LET_THM, ID] THEN
Q.EXISTS_TAC `[]` THEN
SRW_TAC [][] THEN
DISJ1_TAC THEN DISJ2_TAC THEN
FULL_SIMP_TAC (srw_ss()) [finalStateTrans, fstApp, rgr_r9eq] THEN
SRW_TAC [][fstApp, fst1] THEN
METIS_TAC [APPEND_ASSOC]);


val idcNewmPopStk = store_thm
("idcNewmPopStk",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
   MEM q m.final ∧
   ¬(stk=[]) ∧
  (∀e.MEM e stk ⇒ MEM e (stkSymsList m m.next) ∨ (e=x0))
      ⇒
   (ID (newm m (q0',x0,qe)))^* (q,inp,stk) (qe,inp,[])``,

SRW_TAC [][Once RTC_CASES1] THEN
Cases_on `stk` THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `(qe,inp,t)` THEN
SRW_TAC [][]
THENL[
   METIS_TAC [newmFstRule, MEM],

   Cases_on `t` THEN SRW_TAC [][] THEN
   METIS_TAC [MEM, idcNewmPopStkQe, NOT_CONS_NIL]
  ]);




val ruleMemStkSyms = store_thm
("ruleMemStkSyms",
``∀sl.MEM ((x,h,q),q',sl) m.next
      ⇒
   MEM h (stkSymsList m m.next) ∧
   (∀e.MEM e sl ⇒ MEM e (stkSymsList m m.next))``,

   Induct_on `sl` THEN SRW_TAC [][] THEN
   FULL_SIMP_TAC (srw_ss()) [stkSymsList, rgr_r9eq, ssymslApp,
                          stkSymsList'] THEN
   METIS_TAC [APPEND, APPEND_ASSOC]);


val idMemStkSyms = store_thm
("idMemStkSyms",
``m ⊢ (q,s0,stk) → (q',s1,stk') ∧
  (∀e. MEM e stk ⇒ MEM e (stkSymsList m m.next))
       ⇒
    ∀e. MEM e stk' ⇒ MEM e (stkSymsList m m.next)``,

  Cases_on `s0` THEN Cases_on `stk` THEN
  SRW_TAC [][ID] THEN
  METIS_TAC [ruleMemStkSyms, MEM_APPEND]);


val idcMemStkSyms = store_thm
("idcMemStkSyms",
``(ID m)^* (s,inp,st) (s',inp',st') ∧
  (∀e.MEM e st ⇒ MEM e (stkSymsList m m.next))
        ⇒
    (∀e.MEM e st' ⇒ MEM e (stkSymsList m m.next))``,

Q_TAC SUFF_TAC 
  `!x y. (ID m)^* x y ==> 
         !q s0 stk q' s1 stk'.
            (x = (q,s0,stk)) ∧ (y = (q',s1,stk')) ∧
            (∀e.MEM e stk ⇒ MEM e (stkSymsList m m.next)) ⇒
              (∀e.MEM e stk' ⇒ MEM e (stkSymsList m m.next))` 
  THEN1 METIS_TAC [] THEN 
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
METIS_TAC [] THEN
Cases_on `x'` THEN
Cases_on `r` THEN
`∀e. MEM e r' ⇒ MEM e (stkSymsList m m.next)`
  by METIS_TAC [idMemStkSyms] THEN
METIS_TAC []);



val memNewmStkSyms = store_thm
("memNewmStkSyms",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  (m' = (newm m (q0',x0,qe)))
      ⇒
   (MEM x0 (stkSymsList m' m'.next) ∧
    MEM m.ssSym (stkSymsList m' m'.next))``,

  SRW_TAC [][stkSymsList, newm, LET_THM] THEN
  SRW_TAC [][stkSymsList']);



val stkSymsFst = store_thm
("stkSymsFst",
``∀sl stl.∀e.MEM e (stkSymsList' (finalStateTrans q stl sl))
      ⇒
    MEM e sl``,
Induct_on `sl` THEN Induct_on `stl` THEN
SRW_TAC [][finalStateTrans, stkSymsList'] 
THENL[
METIS_TAC [MEM, MEM_APPEND, APPEND],

FULL_SIMP_TAC (srw_ss()) [fst1, stkSymsList', ssymslApp, 
                          finalStateTrans] THEN
METIS_TAC [MEM, MEM_APPEND, APPEND]
]);


val stkSymsNst = store_thm
("stkSymsNst",
``∀sl.∀e.MEM e (stkSymsList' (newStateTrans q sl))
      ⇒
    MEM e sl``,
Induct_on `sl` THEN 
SRW_TAC [][newStateTrans, stkSymsList'] THEN
METIS_TAC [MEM, MEM_APPEND, APPEND]);

val memOldmStkSyms = store_thm
("memOldmStkSyms",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  (m' = (newm m (q0',x0,qe)))
       ⇒
   (∀e.MEM e (stkSymsList m' m'.next)
        ⇒
       (e=x0) ∨ MEM e (stkSymsList m m.next))``,

SRW_TAC [] [stkSymsList] 
THENL[
   FULL_SIMP_TAC (srw_ss()) [newm, LET_THM],

   FULL_SIMP_TAC (srw_ss()) [newm, LET_THM, ssymslApp,
                             stkSymsList'] 
   THENL[
	 FULL_SIMP_TAC (srw_ss()) [stkSymsList] THEN
	 METIS_TAC [stkSymsFst, MEM],

	 FULL_SIMP_TAC (srw_ss()) [stkSymsList] THEN
	 METIS_TAC [stkSymsNst, MEM]
	 ]]);


val lafsImpLaes = store_thm
("lafsImpLaes",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m)
    ⇒
  (x ∈ lafs m ⇒ x ∈ laes (newm m (q0',x0,qe)))``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lafs] THEN
SRW_TAC [][newm, LET_THM] THEN
Q.MATCH_ABBREV_TAC `x ∈ laes <| start := q0'; 
                                ssSym := x0;
				next := d';
				final := [] |>` THEN 
Q.MATCH_ABBREV_TAC `x ∈ laes m'` THEN
`IDC m' (q0',x,[x0]) (m.start,x,m.ssSym::[x0])` by 
(SRW_TAC [][IDC] THEN
SRW_TAC [] [Once RTC_CASES1] THEN
Q.EXISTS_TAC `(m.start,x,[m.ssSym;x0])` THEN
SRW_TAC [][ID] THEN
Cases_on `x` THEN SRW_TAC [][ID] THEN
UNABBREV_ALL_TAC THEN
SRW_TAC [][]) THEN
`IDC m' (m.start,x,[m.ssSym]) (state,[],stack)` 
   by METIS_TAC [idcLafsImpLaes, newm, LET_THM, IDC, APPEND] THEN
`IDC m' (m.start,x,[m.ssSym]++[x0]) (state,[],stack++[x0])` 
  by METIS_TAC [idcStackInsert, IDC, APPEND, newm, LET_THM] THEN

`(MEM x0 (stkSymsList m' m'.next) ∧
    MEM m.ssSym (stkSymsList m' m'.next))`
    by METIS_TAC [memNewmStkSyms, newm, LET_THM, APPEND] THEN
`∀e. MEM e stack ⇒ MEM e (stkSymsList m' m'.next)`
    by METIS_TAC [idcMemStkSyms, MEM, IDC] THEN
`∀e. MEM e stack ⇒ ((e=x0) ∨ MEM e (stkSymsList m m.next))`
       by METIS_TAC [memOldmStkSyms,newm, LET_THM, APPEND] THEN
`(∀e.
          MEM e (stack++[x0]) ⇒
          MEM e (stkSymsList m m.next) ∨ (e = x0))`
  by METIS_TAC  [MEM, MEM_APPEND] THEN
`¬(stack++[x0] = [])` by SRW_TAC [][] THEN
`IDC m' (state,[],stack++[x0]) (qe,[],[])` 
      by METIS_TAC [idcNewmPopStk, IDC, newm, 
                    LET_THM, APPEND] THEN
SRW_TAC [][laes] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `qe` THEN
FULL_SIMP_TAC (srw_ss()) [IDC] THEN
`m'.start = q0'` by SRW_TAC [][Abbr `m'`] THEN
`m'.ssSym = x0` by SRW_TAC [][Abbr `m'`] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [IDC, RTC_RTC, APPEND]);



val newmStartRule = store_thm
("newmStartRule",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m)
       ⇒
  MEM ((NONE,x0,q0'),m.start,[m.ssSym; x0]) 
       (newm m (q0',x0,qe)).next``,

SRW_TAC [][newm, LET_THM]);

val memFslFst = store_thm
("memFslFst",
``∀fl sl'.
    MEM ((NONE,h,q),q',sl) (finalStateTrans qe fl sl')
        ⇒
     MEM q fl``,
Induct_on `sl'` THEN Induct_on `fl` THEN
SRW_TAC [][finalStateTrans, fst1] THEN
METIS_TAC [fstApp, MEM, MEM_APPEND, APPEND, finalStateTrans]);

val slFslNil = store_thm
("slFslNil",
``∀fl sl'.
    MEM ((NONE,h,q),q',sl) (finalStateTrans qe fl sl')
        ⇒
     (sl=[])``,
Induct_on `sl'` THEN Induct_on `fl` THEN
SRW_TAC [][finalStateTrans, fst1] THEN
METIS_TAC [fstApp, MEM, MEM_APPEND, APPEND, finalStateTrans]);



val stEqNst = store_thm
("stEqNst",
``∀sl'.MEM ((NONE,h,q),q',sl) (newStateTrans qe sl')
         ⇒
     (q=qe)``,
Induct_on `sl'` THEN
SRW_TAC [][newStateTrans] THEN
METIS_TAC []);

val slNstNil = store_thm
("slNstNil",
``∀sl'.MEM ((NONE,h,q),q',sl) (newStateTrans qe sl')
         ⇒
     (sl=[])``,
Induct_on `sl'` THEN
SRW_TAC [][newStateTrans] THEN
METIS_TAC []);

val toStEqNst = store_thm
("toStEqNst",
``∀sl'.MEM ((NONE,h,q),q',sl) (newStateTrans qe sl')
         ⇒
     (q'=qe)``,
Induct_on `sl'` THEN
SRW_TAC [][newStateTrans] THEN
METIS_TAC []);





val transStIsFs = store_thm
("transStIsFs",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  MEM ((NONE,h,q),qe,sl) (newm m (q0',x0,qe)).next ∧
  ¬(q=qe)
         ⇒
    MEM q m.final ∧ (sl=[])``,
SRW_TAC [][newm, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [memFslFst, stEqNst, slNstNil, slFslNil]);




val notSomeInpMemFst = store_thm (
"notSomeInpMemFst",
``∀fsl sl'.¬MEM ((SOME h,h',q),q',sl) 
                (finalStateTrans qe fsl sl')``,

Induct_on `fsl` THEN Induct_on `sl'` THEN
SRW_TAC [][finalStateTrans, fst1] THEN
METIS_TAC [fstApp, MEM, MEM_APPEND, APPEND, finalStateTrans]);

val memFst1 = store_thm
("memFst1",
``∀e fsl.MEM e (MAP (fst1 ns ssym) fsl)
        ⇒
    (∃fs.(e=((NONE,ssym,fs),ns,[])) ∧ MEM fs fsl)``,
Induct_on `fsl` THEN SRW_TAC [][fst1] THEN
METIS_TAC []);

val toStEqFst = store_thm
("toStEqNFst",
``∀fsl sl'.MEM ((NONE,h,q),q',sl) (finalStateTrans qe fsl sl')
         ⇒
     (q'=qe)``,
Induct_on `sl'` THEN
SRW_TAC [][finalStateTrans, fst1] THEN
FULL_SIMP_TAC (srw_ss()) [finalStateTrans] THEN
IMP_RES_TAC memFst1 THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [memFst1]);




val notSomeInpMemNst = store_thm (
"notSomeInpMemNst",
``∀fsl sl'.¬MEM ((SOME h,h',q),q',sl) 
                (newStateTrans qe sl')``,

Induct_on `sl'` THEN
SRW_TAC [][newStateTrans] THEN
METIS_TAC [MEM, MEM_APPEND, APPEND, newStateTrans]);


val notSomeMemNewm = store_thm
("notSomeMemNewm",
 ``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) 
      ⇒
    ¬MEM ((SOME h,h',q),qe,sl) (newm m (q0',x0,qe)).next``,

SRW_TAC [][newm, LET_THM] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [notSomeInpMemFst, notSomeInpMemNst]);


val memToQeNewm = store_thm
("memToQeNewm",
 ``¬(x0 ∈ stkSyms m) ∧
   ¬(q0' ∈ states m) ∧
   ¬(qe ∈ states m) ∧
   ¬(q0' = qe) ∧
   MEM ((NONE,h,qe),q,sl) (newm m (q0',x0,qe)).next
      ⇒
    (q=qe) ∧ (sl=[])``,
SRW_TAC [][newm, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [memFslFst,slNstNil,toStEqNst]);
    


val notSomeMemQeNewm = store_thm
("notSomeMemQeNewm",
 ``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) 
      ⇒
    ¬MEM ((SOME h,h',qe),q,sl) (newm m (q0',x0,qe)).next``,

SRW_TAC [][newm, LET_THM] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [notSomeInpMemFst, notSomeInpMemNst, memToQeNewm]);



val listQeTransInpSame = store_thm 
("listQeTransInpSame",
``∀dl qe inp stk inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  ID (newm m (q0',x0,qe)) ⊢ 
        dl ◁  (qe,inp,stk) → (qe,inp',stk')
        ⇒
      (inp=inp')``,
Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN
Cases_on `r` THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`r'`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `inp` THEN Cases_on `stk` THEN 
FULL_SIMP_TAC (srw_ss()) [ID] THEN
METIS_TAC [notSomeMemQeNewm, memToQeNewm]);



val idFsToQeInpSame = store_thm 
("idFsToQeInpSame",
``∀dl qe inp stk inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  MEM qf m.final ∧
  newm m (q0',x0,qe) ⊢ (qf,inp,stk) → (qe,inp',stk')
        ⇒
      (inp=inp')``,
SRW_TAC [][newm, LET_THM] THEN
Cases_on `inp` THEN Cases_on `stk` THEN 
FULL_SIMP_TAC (srw_ss()) [ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [notSomeInpMemFst, notSomeInpMemNst]);

val idFromQeInpSame = store_thm 
("idFromQeInpSame",
``∀dl qe inp stk inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  newm m (q0',x0,qe) ⊢ (qe,inp,stk) → (q',inp',stk')
        ⇒
      (inp=inp') ∧ (q'=qe)``,
SRW_TAC [][newm, LET_THM] THEN
Cases_on `inp` THEN Cases_on `stk` THEN 
FULL_SIMP_TAC (srw_ss()) [ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [notSomeInpMemFst, notSomeInpMemNst,
	   toStEqFst, toStEqNst]);


val listQeTrans = store_thm 
("listQeTrans",
``∀dl qe inp stk st inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  ID (newm m (q0',x0,qe)) ⊢ 
        dl ◁  (qe,inp,stk) → (st,inp',stk')
        ⇒
      (st=qe)``,
Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN
Cases_on `r` THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`q`,`q'`,`r'`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `inp` THEN Cases_on `stk` THEN 
FULL_SIMP_TAC (srw_ss()) [ID] THEN
METIS_TAC [notSomeMemQeNewm, memToQeNewm]);



val idQeTrans = store_thm
("idQeTrans",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  newm m (q0',x0,qe) ⊢ (q,inp,stk) → (qe,q'',r')
        ⇒
    (q''=inp) ∧ (r'=TL stk)``,

Cases_on `inp` THEN Cases_on `stk` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][]
THENL[
Cases_on `q=qe` THEN
SRW_TAC [][] THEN
METIS_TAC [transStIsFs, APPEND, memToQeNewm],
   
METIS_TAC [notSomeMemNewm],

METIS_TAC [notSomeMemNewm],

Cases_on `q=qe` THEN
SRW_TAC [][] THEN
METIS_TAC [transStIsFs, APPEND, memToQeNewm]]);
  
val listFsExists = store_thm 
("listFsExists",
``∀dl q inp stk qe inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  ID (newm m (q0',x0,qe)) ⊢ 
        dl ◁  (q,inp,stk) → (qe,inp',stk') ∧ ¬(q=qe)
        ⇒
     ∃qf sk.MEM (qf,inp',sk) dl ∧ MEM qf m.final``,

Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN
Cases_on `r` THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`q'`, `q''`, `r'`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `¬(q'=qe)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [] THEN1 METIS_TAC [] THEN
`q''=inp` by METIS_TAC [idQeTrans] THEN
SRW_TAC [][] THEN
`inp=inp'` by METIS_TAC [listQeTransInpSame, HD, 
			 listderiv_def] THEN
Cases_on `inp` THEN
Cases_on `stk` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][] THEN
METIS_TAC [transStIsFs]);


val listQeOnly = store_thm 
("listQeOnly",
``∀dl inp stk qe q' inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  ID (newm m (q0',x0,qe)) ⊢ 
        dl ◁  (qe,inp,stk) → (q',inp,stk')
        ⇒
    (∀e.MEM e dl ⇒ ∃i sk.(e=(qe,inp,sk)))``,

Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[
  Cases_on `h` THEN
  Cases_on `r` THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`r'`, `qe`] MP_TAC) THEN
  SRW_TAC [][] THEN
  METIS_TAC [listQeTransInpSame, listQeTrans, rtc2list_exists',
	   RTC_RULES],

  Cases_on `h` THEN
  Cases_on `r` THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`r'`, `qe`] MP_TAC) THEN
  SRW_TAC [][] THEN
  `(q=qe) ∧ (q''=inp)` by METIS_TAC [listQeTransInpSame, 
				     listQeTrans, rtc2list_exists',
				     RTC_RULES] THEN
  METIS_TAC []]);

    

val rtc2listRtcHdLast = store_thm ("rtc2listRtcHdLast",
``!t.rtc2list R t ==> ~(t=[]) ==>
   RTC R (HD t) (LAST t)``,
    Induct_on `t` THEN SRW_TAC [] [rtc2list_def] THEN
    SRW_TAC [] [RTC_RULES] THEN
    Cases_on `t` THEN
    FULL_SIMP_TAC (srw_ss()) [rtc2list_def, RTC_RULES] THEN
    METIS_TAC [RTC_RULES]);


val listFsExists' = store_thm 
("listFsExists'",
``∀dl q inp stk qe inp' stk'.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  ID (newm m (q0',x0,qe)) ⊢ 
        dl ◁  (q,inp,stk) → (qe,inp',stk') ∧ ¬(q=qe)
        ⇒
     ∃p s qf sk.(dl = p ++ [(qf,inp',sk)] ++ s) ∧
                MEM qf m.final ∧
                (∀e.MEM e s ⇒ ∃i sk.(e=(qe,i,sk)))``,

Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN
Cases_on `r` THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`q'`, `q''`, `r'`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `¬(q'=qe)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [APPEND] THEN
`q''=inp` by METIS_TAC [idQeTrans] THEN
SRW_TAC [][] THEN
`inp=inp'` by METIS_TAC [listQeTransInpSame, HD, 
			 listderiv_def] THEN
Cases_on `inp` THEN
Cases_on `stk` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][] THEN
`MEM q m.final` by METIS_TAC [transStIsFs] 
THENL[
`(ID (newm m (q0',x0,q')))^*
            (q',[],sl ++ t') (q',[],stk')`
  by METIS_TAC [rtc2list_def, rtc2listRtcHdLast, HD] THEN
`ID (newm m (q0',x0,q')) ⊢ ((q',[],sl ++ t')::t) ◁
            (q',[],sl ++ t') → (q',[],stk')` 
    by METIS_TAC [listderiv_def, HD] THEN
`∀e. MEM e ((q',[],sl ++ t')::t) ⇒ ∃i sk. e = (q',[],sk)` 
    by METIS_TAC [listQeOnly] THEN

MAP_EVERY Q.EXISTS_TAC [`[]`, `((q',[],sl ++ t')::t)`,
			`q`, `h::t'`] THEN
SRW_TAC [][] THEN
METIS_TAC [MEM],

`(ID (newm m (q0',x0,q')))^*
            (q',h::t',sl ++ t'') (q',h::t',stk')`
  by METIS_TAC [rtc2list_def, rtc2listRtcHdLast, HD] THEN
`ID (newm m (q0',x0,q')) ⊢ ((q',h::t',sl ++ t'')::t) ◁
            (q',h::t',sl ++ t'') → (q',h::t',stk')` 
    by METIS_TAC [listderiv_def, HD] THEN
`∀e. MEM e ((q',h::t',sl ++ t'')::t) ⇒ ∃i sk. e = (q',h::t',sk)` 
    by METIS_TAC [listQeOnly] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`, `((q',h::t',sl ++ t'')::t)`,
			`q`, `h'::t''`] THEN
SRW_TAC [][] THEN
METIS_TAC [MEM]]);






val rtc2list_mem = store_thm
("rtc2list_mem",
``∀l e1 e2.R ⊢ l ◁ e1 → e2 ∧
    MEM e' l
       ⇒
    R^* e1 e' ∧ R^* e' e2``,

  Induct_on `l` THEN 
  SRW_TAC [][rtc2list_def, listderiv_def] THEN1      
   METIS_TAC [RTC_RULES] THEN1
   METIS_TAC [HD, rtc2listRtcHdLast, NOT_CONS_NIL] THEN
  Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`LAST (h::t)`] MP_TAC) THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  METIS_TAC [RTC_RULES]);


val idcNewmFinalToQe = store_thm
("idcNewmFinalToQe",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0'=qe) ∧
  (ID (newm m (q0',x0,qe)))^* (st,inp,sk) (qe,inp',sk') 
     ⇒
   (st = qe) ∨ 
   ∃y st' i s.(ID (newm m (q0',x0,qe)))^* (st,inp,sk) y ∧
            (ID (newm m (q0',x0,qe)))^* y (qe,inp',sk') ∧
            (y = (st',i,s)) ∧ MEM st' m.final``,

SRW_TAC [][] THEN
`∃dl.ID (newm m (q0',x0,qe)) ⊢ dl ◁ (st,inp,sk) → (qe,inp',sk')`
   by METIS_TAC [rtc2list_exists'] THEN
Cases_on `st=qe` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`∃qf i sk. MEM (qf,i,sk) dl ∧ MEM qf m.final` 
    by METIS_TAC [listFsExists] THEN
METIS_TAC [rtc2list_mem]);


val idcNewmFinalToQe' = store_thm
("idcNewmFinalToQe'",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0'=qe) ∧
  (ID (newm m (q0',x0,qe)))^* (st,inp,sk) (qe,inp',sk') 
     ⇒
   (st = qe) ∨ 
   ∃y st' i s sk''.
         (ID (newm m (q0',x0,qe)))^* (st,inp,sk) y ∧
         (ID (newm m (q0',x0,qe))) y (qe,inp',sk'') ∧
         (ID (newm m (q0',x0,qe)))^* (qe,inp',sk'') (qe,inp',sk') ∧
         (y = (st',i,s)) ∧ MEM st' m.final``,

SRW_TAC [][] THEN
`∃dl.ID (newm m (q0',x0,qe)) ⊢ dl ◁ (st,inp,sk) → (qe,inp',sk')`
   by METIS_TAC [rtc2list_exists'] THEN
Cases_on `st=qe` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`∃p s qf sk.
           (dl = p ++ [(qf,inp',sk)] ++ s) ∧
           MEM qf m.final ∧
           ∀e. MEM e s ⇒ ∃i sk. e = (qe,i,sk)` 
    by METIS_TAC [listFsExists'] THEN
SRW_TAC [][] THEN
Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) []
THENL[
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `(qf,inp',sk'') = (qe,inp',sk')` 
	  by METIS_TAC [last_append, NOT_CONS_NIL, LAST_DEF] THEN
      FULL_SIMP_TAC (srw_ss()) [states],
      
      `∃i sk. h = (qe,i,sk)` by METIS_TAC [] THEN
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`qf`, `inp'`, `sk''`, `sk'''`] THEN
      SRW_TAC [][] 
      THENL[
         METIS_TAC [rtc2list_mem, listderiv_def, MEM, MEM_APPEND],

	 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	 `rtc2list (ID (newm m (q0',x0,qe)))
            ([(qf,inp',sk'')] ++ (qe,i,sk''')::t)`
	     by METIS_TAC [NOT_CONS_NIL, APPEND,APPEND_ASSOC,
			   rtc2list_distrib_append_snd] THEN
	 Cases_on `t` THEN 
	 FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
	 `newm m (q0',x0,qe) ⊢ (qf,inp',sk'') → (qe,i,sk''')` 
	     by METIS_TAC [rtc2list_def, 
			   rtc2list_distrib_append_snd,
			   MEM, MEM_APPEND, APPEND,listderiv_def] THEN
	 METIS_TAC [idFsToQeInpSame],

	 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	 `rtc2list (ID (newm m (q0',x0,qe)))
            ((qe,i,sk''')::t)`
	     by METIS_TAC [NOT_CONS_NIL,
			   rtc2list_distrib_append_snd] THEN
	 Cases_on `t` THEN 
	 FULL_SIMP_TAC (srw_ss()) [rtc2list_def] 
	 THENL[
	       `LAST ([(qf,inp',sk'')] ++ [(qe,i,sk''')])=(qe,inp',sk')`
		   by METIS_TAC [last_append, LAST_DEF,
				 NOT_CONS_NIL] THEN
	       `(qe,i,sk''')=(qe,inp',sk')` 
		   by METIS_TAC [last_append, LAST_DEF,
				 NOT_CONS_NIL] THEN
	       FULL_SIMP_TAC (srw_ss()) [],

	       Cases_on `h` THEN
	       Cases_on `r` THEN
	       `(q'=i) ∧ (q=qe)`by METIS_TAC [idFromQeInpSame] THEN
	       SRW_TAC [][] THEN
`rtc2list (ID (newm m (q0',x0,q)))
            ([(qf,inp',sk'')] ++ (q,i,sk''')::(q,i,r')::t')`
    by METIS_TAC [NOT_CONS_NIL, APPEND,APPEND_ASSOC,
			   rtc2list_distrib_append_snd] THEN
FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN

`i=inp'` by METIS_TAC [idFsToQeInpSame] THEN
SRW_TAC [][] THEN
`(p ++ [(qf,i,sk'')] ++ (q,i,sk''')::(q,i,r')::t') =
(p ++ [(qf,i,sk'')] ++ [(q,i,sk''')])++(q,i,r')::t'`
	 by METIS_TAC [APPEND_ASSOC, APPEND] THEN
`LAST ((q,i,r')::t') =(q,i,sk')` by METIS_TAC [last_append,
					       NOT_CONS_NIL] THEN
METIS_TAC [rtc2listRtcHdLast, HD, RTC_RULES, NOT_CONS_NIL]
]]]);



val x0TransStIsQe = store_thm
("x0TransStIsQe",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  newm m (q0',x0,qe) ⊢ (q,inp,stk) → (q',q'',r') ∧
  MEM x0 stk ∧
  ¬MEM x0 r'
       ⇒
    (q'=qe)``,

SRW_TAC [] [newm, LET_THM] THEN
Cases_on `inp` THEN Cases_on `stk` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] 
THENL[

FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
METIS_TAC [],

METIS_TAC [toStEqFst], 

METIS_TAC [toStEqNst],

FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
METIS_TAC [],

METIS_TAC [notSomeInpMemFst],

METIS_TAC [notSomeInpMemNst], 

FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
METIS_TAC [],

METIS_TAC [toStEqFst], 

METIS_TAC [toStEqNst]]);



val newmNullStkStQeLd = store_thm
("newmNullStkStQeLd",
``∀dl q inp stk.
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  ID (newm m (q0',x0,qe)) ⊢ 
        dl ◁  (q,inp,stk) → (state,[],[]) ∧
  MEM x0 stk
       ⇒
     (state=qe)``,

Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[

      SRW_TAC [][] THEN METIS_TAC [MEM],

      Cases_on `h` THEN
      Cases_on `r` THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`q'`, `q''`, `r'`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `MEM x0 r'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [listderiv_def, listQeTrans, HD, x0TransStIsQe]
      ]);



val newmNullStkStQe = store_thm
("newmNullStkStQe",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  (ID (newm m (q0',x0,qe)))^* (q,inp,stk++[x0]) (state,[],[])
       ⇒
     (state=qe)``,
SRW_TAC [][] THEN
`∃dl.ID (newm m (q0',x0,qe)) ⊢ dl ◁ 
                               (q,inp,stk++[x0]) → (state,[],[])`
   by METIS_TAC [rtc2list_exists'] THEN
METIS_TAC [newmNullStkStQeLd, MEM, MEM_APPEND]);



val idNewmImpOldm = store_thm
("idNewmImpOldm",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  newm m (q0',x0,qe) ⊢ (q,i,s) → (q',i',s') ∧
  q' ∈ states m
        ⇒
    (q=q0') ∨ 
    (q ∈ states m ∧
    m ⊢ (q,i,s) → (q',i',s'))``,

SRW_TAC [][newm, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `i` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [memFslFst, toStEqFst, notSomeInpMemFst, toStEqNst,
	   notSomeInpMemNst]);


val idStatesMem = store_thm
("idStatesMem",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
  newm m (q0',x0,qe) ⊢ (q,s,stk) → (q',s',stk') ∧
  q ∈ states m
       ⇒
     (q' = qe) ∨ (q' ∈ states m)``,

Cases_on `s` THEN Cases_on `stk` THEN
SRW_TAC [][newm, LET_THM, ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [toStEqFst, toStEqNst, notSomeInpMemNst, 
	   notSomeInpMemFst]);



val idcNewmImpOldm = store_thm
("idcNewmImpOldm",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
   (ID (newm m (q0',x0,qe)))^* (q,i,s) (q',i',s') ∧
   q' ∈ states m ∧
   q ∈ states m
        ⇒
    (ID m)^* (q,i,s) (q',i',s')``,

Q_TAC SUFF_TAC 
  `∀x y. (ID (newm m (q0',x0,qe)))^* x y ⇒
         ¬(x0 ∈ stkSyms m) ⇒
         ¬(q0' ∈ states m) ⇒
         ¬(qe ∈ states m)  ⇒
         ¬(q0' = qe) ⇒
         ∀q s0 stk q' s1 stk'.
            (x = (q,s0,stk)) ∧ (y = (q',s1,stk')) ∧
             q' ∈ states m ∧ q ∈ (states m)
                   ⇒
        	(ID m)^* (q,s0,stk) (q',s1,stk')` THEN1 
METIS_TAC [] THEN 
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [RTC_RULES] THEN
Cases_on `x'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`q'' ∈ states m ∨ (q'' = qe)` by METIS_TAC [idStatesMem]
THENL[
      `∃l.ID (newm m (q0',x0,qe)) ⊢ l ◁ 
                          (q'',q''',r') → (q',s1,stk')`
	    by METIS_TAC [rtc2list_exists'] THEN
      `q'' ∈ states m` by METIS_TAC [idStatesMem] THEN
      METIS_TAC [RTC_RULES, idNewmImpOldm],


      SRW_TAC [][] THEN
      `∃l.ID (newm m (q0',x0,q'')) ⊢ l ◁ 
                          (q'',q''',r') → (q',s1,stk')`
	    by METIS_TAC [rtc2list_exists'] THEN
      METIS_TAC [listQeTrans]
      ]);


val idNewmFstStep = store_thm
("idNewmFstStep",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
   newm m (q0',x0,qe) ⊢ (q0',i,[x0]) → (q,q'',r')
         ⇒
    (q = m.start) ∧ (q'' = i) ∧ (r' = m.ssSym::[x0])``,

Cases_on `i` THEN
SRW_TAC [][ID] THEN
FULL_SIMP_TAC (srw_ss()) [newm, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [memFslFst,stEqNst,notSomeInpMemFst,notSomeInpMemNst]);


val newmFstStep = store_thm
("newmFstStep",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe) ∧
   (ID (newm m (q0',x0,qe)))^* 
          (q0',i,[x0]) (q',i',s') ∧
   ¬(q0' = q')
         ⇒ 
     ID (newm m (q0',x0,qe))
          (q0',i,[x0]) (m.start,i,m.ssSym::[x0]) ∧ 
    (ID (newm m (q0',x0,qe)))^* 
          (m.start,i,m.ssSym::[x0]) (q',i',s')``,

SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC 
THENL[
   FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
   SRW_TAC [][] THEN
   Cases_on `i` THEN
   FULL_SIMP_TAC (srw_ss()) [newm, LET_THM, ID],

   `((q0',i,[x0])=(q',i',s')) ∨
    ∃u.ID (newm m (q0',x0,qe)) (q0',i,[x0]) u ∧
    (ID (newm m (q0',x0,qe)))^* u (q',i',s')`
       by METIS_TAC [RTC_CASES1] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN
   SRW_TAC [][] THEN
   Cases_on `u` THEN
   Cases_on `r` THEN
   METIS_TAC [idNewmFstStep]]);


val idStkPop = store_thm
("idStkPop",
``m ⊢ (q,i,p ++ [sym] ++ s) → (q',i',stk') ∧
  ¬MEM sym p ∧
  ¬(sym ∈ stkSyms m)
        ⇒
    ∃p'.(stk' = p' ++ [sym] ++ s) ∧ ¬MEM sym p' ∧
         m ⊢ (q,i,p) → (q',i',p')``,
Cases_on `i` THEN Cases_on `p` THEN
SRW_TAC [][ID] THEN
MAGIC);



val idcStkPop = store_thm
("idcStkPop",
``∀l q i s q' i' stk' p.
     ID m ⊢ l ◁ (q,i,p++[sym]++s) → (q',i',stk') ∧
     ¬MEM sym p ∧
     ¬(sym ∈ stkSyms m)
           ⇒
        ∃l' p'.
          (stk' = p' ++ [sym] ++ s) ∧
          ¬MEM sym p' ∧
          ID m ⊢ l' ◁ (q,i,p) → (q',i',p')``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [listderiv_def],


      Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def, SNOC] THEN
	    SRW_TAC [][] THEN
	    MAP_EVERY Q.EXISTS_TAC [`[(q,i,p)]`,`p`] THEN
	    SRW_TAC [][],

	    FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND] THEN
	    Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  `∃p'.(stk' = p' ++ [sym] ++ s) ∧ ¬MEM sym p' ∧
                     m ⊢ (q,i,p) → (q',i',p')` 
		      by METIS_TAC [idStkPop] THEN
		  SRW_TAC [][] THEN
		  Q.EXISTS_TAC `(q,i,p)::[(q',i',p')]` THEN
		  SRW_TAC [][],

		  `LAST (h::h'::t') = x` by MAGIC THEN
		  Cases_on `x` THEN
		  Cases_on `r` THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN [`q`, `i`,`s`,
					       `q''`, `q'''`,`r'`,
					       `p`] 
				MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  `rtc2list (ID m) (h'::t')` by MAGIC THEN
		  `∃l' p'.(r' = p' ++ [sym] ++ s) ∧ ¬MEM sym p' ∧
                          rtc2list (ID m) l' ∧ (HD l' = (q,i,p)) ∧
                          (LAST l' = (q'',q''',p'))`
		  by METIS_TAC [] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  MAGIC]]]);


val newmssSym = store_thm
("newmssSym",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) 
          ⇒
    ((newm m (q0',x0,qe)).ssSym=x0)``,
SRW_TAC [][newm, LET_THM]);

val newmstart = store_thm
("newmstart",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) 
          ⇒
    ((newm m (q0',x0,qe)).start=q0')``,
SRW_TAC [][newm, LET_THM]);



(*
If M1 accepts x by empty stack, it is easy to show that the
sequence of moves must be one move by rule1, then a sequence
of moves by rule2 in which M1 simulates acceptance of x by M2,
followed by the erasure of M1s stack using rules3 and 4.
Thus x must be in L(M2).
*)

val laesImpLafs = store_thm
("laesImpLafs",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qe ∈ states m) ∧
  ¬(q0' = qe)
    ⇒
  (x ∈ laes (newm m (q0',x0,qe)) ⇒ x ∈ lafs m)``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lafs, laes, IDC] THEN
`(newm m (q0',x0,qe)).ssSym=x0` by METIS_TAC [newmssSym] THEN
`state=qe` by METIS_TAC [newmNullStkStQe, APPEND] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`¬((newm m (q0',x0,qe)).start=qe)` by METIS_TAC [newmstart] THEN
`∃y i st' s sk''.
         (ID (newm m (q0',x0,qe)))^* 
             ((newm m (q0',x0,qe)).start,x,[x0]) y ∧
          newm m (q0',x0,qe) ⊢ y → (qe,[],sk'') ∧
         (ID (newm m (q0',x0,qe)))^* (qe,[],sk'') (qe,[],[]) ∧
         (y = (st',i,s)) ∧ MEM st' m.final` 
    by METIS_TAC [idcNewmFinalToQe'] THEN
SRW_TAC [][] THEN
`i=[]` by METIS_TAC [idFsToQeInpSame] THEN
SRW_TAC [][] THEN
`st' ∈ states m` by FULL_SIMP_TAC (srw_ss()) [states] THEN
`m.start ∈ states m` by FULL_SIMP_TAC (srw_ss()) [states] THEN
`(newm m (q0',x0,qe)).start=q0'` by METIS_TAC [newmstart] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`¬(q0'=st')` by METIS_TAC [] THEN
`newm m (q0',x0,qe) ⊢
   (q0',x,[x0]) → (m.start,x,[m.ssSym; x0]) ∧
    (ID (newm m (q0',x0,qe)))^* (m.start,x,[m.ssSym; x0])
                                 (st',[],s)`
    by METIS_TAC [newmFstStep] THEN
`(ID m)^* (m.start,x,[m.ssSym; x0]) (st',[],s)` 
     by METIS_TAC [idcNewmImpOldm] THEN
`m.ssSym ≠ x0` by FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
IMP_RES_TAC idcStkPop THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`[m.ssSym]`] MP_TAC) THEN
SRW_TAC [][] THEN
`∃l. ID m ⊢ l ◁ (m.start,x,[m.ssSym; x0]) → (st',[],s)` 
    by METIS_TAC [rtc2list_exists'] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s`, `[]`, `st'`, `m.start`,`l`,
			     `[]`,`x`] MP_TAC) THEN
SRW_TAC [][] THEN
METIS_TAC [HD, rtc2listRtcHdLast, NOT_CONS_NIL, rtc2list_def,
	   listderiv_def]);


val thm5_1 = store_thm 
("thm5_1",
``INFINITE (SYMUNIV : 'ssym set) ∧ INFINITE (STUNIV : 'state set) 
      ⇒
     ∀m.∃m'. (lafs (m:('isym, 'ssym, 'state) pda) = 
             laes (m':('isym, 'ssym, 'state) pda))``,

SRW_TAC [] [EQ_IMP_THM, EXTENSION] THEN
`FINITE (stkSyms m)` 
     by METIS_TAC [finiteStkSyms, FINITE_LIST_TO_SET] THEN
`?x0.x0 IN SYMUNIV ∧ ~(x0 IN (stkSyms m))` 
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_ssym_exists] THEN
`FINITE (states m)` 
     by METIS_TAC [finiteStates, FINITE_LIST_TO_SET] THEN
`?q0.q0 IN STUNIV ∧ ~(q0 IN (states m))` 
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists] THEN
`?qe.qe IN STUNIV ∧ ~(qe IN (states m)) ∧ ¬(q0=qe)` 
    by MAGIC
(* METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists,
		  FINITE_SING]*) THEN
Q.EXISTS_TAC `newm m (q0,x0,qe)` THEN
SRW_TAC [][] THEN
METIS_TAC [laesImpLafs, lafsImpLaes]);


val toFinalStateTrans = Define
`toFinalStateTrans x0 qf st = ((NONE,x0,st),qf,[])`;

val newm' = Define
`newm' (p:('isym, 'ssym, 'state) pda) 
      (q0':'state,x0:'ssym,qf:'state) = 
let d = [((NONE:'isym option,x0,q0'),(p.start,p.ssSym::[x0]))] ++
        p.next ++
        MAP (toFinalStateTrans x0 qf) (statesList p p.next)
in
      <| start := q0';  ssSym := x0;  
         next := d; final := ([qf]:'state list) |>`;




(*
1-step transitions in the old PDA are still
valid in the new PDA.
*)
val idLaesImpLafs' = store_thm
("idLaesImpLafs'",
``∀x y. (m:('i,'s,'st)pda) ⊢ x → y ∧ 
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m) 
      ⇒
    newm' m (q0',x0,qf) ⊢ x → y``,

SRW_TAC [][newm', LET_THM] THEN
Cases_on `x` THEN Cases_on `r` THEN
Cases_on `y` THEN Cases_on `r` THEN
Cases_on `q'` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [ID]);


(*
m-step transitions in the old PDA are still
valid in the new PDA.
*)
val idcLaesImpLafs' = store_thm
("idcLaesImpLafs'",
``∀x y.(ID m)^* x y ⇒
  ¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m)
      ⇒
   (ID (newm' m (q0',x0,qf)))^* x y``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q_TAC SUFF_TAC `newm' m (q0',x0,qf) ⊢ x → x'` THEN
METIS_TAC [RTC_RULES, idLaesImpLafs']);


val finalStateRule = store_thm 
("finalStateRule",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m) ∧
  (m' = (newm' m (q0',x0,qf)))  ∧
  (MEM state (statesList m m.next))
     ⇒
  MEM ((NONE,x0,state),qf,[]) m'.next``,

SRW_TAC [][newm', LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][toFinalStateTrans] THEN
METIS_TAC []);


val statesListApp = store_thm
("statesListApp",
``∀p1 p2.statesList' (p1++p2) = 
           statesList' p1 ++ statesList' p2``,

Induct_on `p1` THEN Induct_on `p2` THEN
SRW_TAC [][statesList'] THEN
Cases_on `h'` THEN Cases_on `r`THEN
Cases_on `q` THEN Cases_on `r` THEN
SRW_TAC [][statesList']);



val memStateRule = store_thm
("memStateRule",
 ``MEM ((x,h,st),q,sl) m.next
    ⇒
   MEM st (statesList m m.next) ∧
   MEM q (statesList m m.next)``,
 
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [statesList] THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, statesListApp, 
                            statesList'] THEN 
  METIS_TAC [APPEND, APPEND_ASSOC]);
  

val memState = store_thm
("memState",
``IDC m (st,inp,stk) (st',inp',stk')
      ⇒
   (st=st') ∨ 
   ((MEM st (statesList m m.next)) ∧
   (MEM st' (statesList m m.next)))``,

  Cases_on `st=st'` THEN
  SRW_TAC [][] 
  THENL[
  
     FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1, IDC] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     Cases_on `u` THEN
     Cases_on `r` THEN
     Cases_on `inp` THEN
     Cases_on `stk` THEN
     FULL_SIMP_TAC (srw_ss()) [ID] THEN
     METIS_TAC [memStateRule],

     FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES2, IDC] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     Cases_on `u` THEN
     Cases_on `r` THEN
     Cases_on `q'` THEN
     Cases_on `r'` THEN
     FULL_SIMP_TAC (srw_ss()) [ID] THEN
     METIS_TAC [memStateRule]
 ]);


val memStartStateNewm' = store_thm
("memStartStateNewm'",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m) ∧
  (m'=(newm' m (q0',x0,qf)))
     ⇒
   MEM m.start (statesList m' m'.next)``,

SRW_TAC [][newm', LET_THM] THEN
SRW_TAC [][statesList] THEN
METIS_TAC [rich_listTheory.CONS_APPEND, statesListApp, 
           statesList', MEM]);


val laesImpLafs' = store_thm
("laesImpLafs'",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m)
    ⇒
  (x ∈ laes m ⇒ x ∈ lafs (newm' m (q0',x0,qf)))``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][newm', LET_THM] THEN
Q.MATCH_ABBREV_TAC `x ∈ lafs <| start := q0'; 
                                ssSym := x0;
				next := d';
				final := [qf] |>` THEN 
Q.MATCH_ABBREV_TAC `x ∈ lafs m'` THEN
`IDC m' (q0',x,[x0]) (m.start,x,m.ssSym::[x0])` by 
(SRW_TAC [][IDC] THEN
SRW_TAC [] [Once RTC_CASES1] THEN
Q.EXISTS_TAC `(m.start,x,[m.ssSym;x0])` THEN
SRW_TAC [][ID] THEN
Cases_on `x` THEN SRW_TAC [][ID] THEN
UNABBREV_ALL_TAC THEN
SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [laes] THEN
`IDC m' (m.start,x,[m.ssSym]) (state,[],[])` 
   by METIS_TAC [idcLaesImpLafs', newm', LET_THM, IDC, APPEND] THEN
SRW_TAC [][lafs] THEN
`IDC m' (m.start,x,m.ssSym::[x0]) 
        (state,[],[x0])` 
          by METIS_TAC [IDC, APPEND, idcStackInsert] THEN
`MEM m.start (statesList m m.next)` 
   by MAGIC THEN
 (* METIS_TAC [memStartStateNewm', Abbr `m'`, newm', Abbr `d'`,
                 APPEND, LET_THM] *)
`MEM state (statesList m m.next)` 
    by METIS_TAC [memState] THEN
`MEM ((NONE,x0,state),qf,[]) m'.next` 
     by MAGIC THEN
(* METIS_TAC [finalStateRule, Abbr `m'`, LET_THM, newm', 
                   APPEND] *)
`ID m' (state,[],[x0]) (qf,[],[])`
  by SRW_TAC [][ID] THEN
MAP_EVERY Q.EXISTS_TAC [`qf`, `[]`]  THEN
SRW_TAC [][] THEN
`IDC m' (state,[],[x0]) (qf,[],[])` 
    by SRW_TAC [][RTC_RULES, IDC] THEN
`MEM qf m'.final` by SRW_TAC [][Abbr `m'`] THEN
`m'.start = q0'` by SRW_TAC [][Abbr `m'`] THEN
`m'.ssSym = x0` by SRW_TAC [][Abbr `m'`] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [RTC_RTC, IDC]
)



val notSomeInpMemFst' = store_thm (
"notSomeInpMemFst'",
``∀fsl sl'.¬MEM ((SOME h,h',q),q',sl) 
                (MAP (toFinalStateTrans x0 qf) stl)``,

Induct_on `stl` THEN
SRW_TAC [][toFinalStateTrans]);




val toStEqFs = store_thm (
"toStEqFs",
``∀fsl sl'.MEM ((NONE,h',q),q',sl) 
                (MAP (toFinalStateTrans x0 qf) stl)
               ⇒
            (q'=qf) ∧ (sl=[]) ∧ (h'=x0)``,

Induct_on `stl` THEN
SRW_TAC [][toFinalStateTrans] THEN
METIS_TAC []);


Induct_on `stl` THEN
SRW_TAC [][toFinalStateTrans] THEN
METIS_TAC []);


val toFsStk = store_thm
("toFsStk",
``∀q i s i' s'.
   x0 ∉ stkSyms m ∧
   q0' ∉ states m ∧
   qf ∉ states m ∧
   newm' m (q0',x0,qf) ⊢ (q,i,s) → (qf,i',s')
         ⇒
     ∃sfx.(s=[x0]++sfx) ∧ (s'=sfx)``,

Cases_on `i` THEN Cases_on `s` THEN
SRW_TAC [][newm', LET_THM, ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN 
METIS_TAC [toStEqFs, notSomeInpMemFst', APPEND]);


val idStatesMem' = store_thm
("idStatesMem'",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m ∧
  (q0' ≠ qf) ∧
  newm' m (q0',x0,qf) ⊢ (q,s,stk) → (q',s',stk') ∧
  q ∈ states m
       ⇒
     (q' = qf) ∨ (q' ∈ states m)``,

Cases_on `s` THEN Cases_on `stk` THEN
SRW_TAC [][newm', LET_THM, ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [toStEqFs, notSomeInpMemFst']);


val idNewm'ImpOldm = store_thm
("idNewm'ImpOldm",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m ∧
  newm' m (q0',x0,qf) ⊢ (q,i,s) → (q',i',s') ∧
  q' ∈ states m
        ⇒
    (q=q0') ∨ 
    (q ∈ states m ∧
    m ⊢ (q,i,s) → (q',i',s'))``,

SRW_TAC [][newm', LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `i` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN
METIS_TAC [notSomeInpMemFst', toStEqFs]);



val memFslFst' = store_thm
("memFslFst'",
``∀fl sl'.
    MEM ((NONE,h,q),q',sl) (MAP (toFinalStateTrans x0 qf) sl')
        ⇒
     MEM q sl'``,
Induct_on `sl'` THEN
SRW_TAC [][toFinalStateTrans] THEN
METIS_TAC []);

val idcNewm'EndSt = store_thm
("idNewm'EndSt",
``∀i s q' i' s'.
     x0 ∉ stkSyms m ∧
     q0' ∉ states m ∧
     qf ∉ states m ∧
     (qf ≠ q0')
          ⇒
       ¬(newm' m (q0',x0,qf) ⊢ (qf,i,s) → (q',i',s'))``,

SRW_TAC [][newm', LET_THM] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
Cases_on `i` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [states] THEN
      METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states] THEN
      METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states] THEN
      METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in]
      ]);



val idcNewm'ImpOldm = store_thm
("idcNewm'ImpOldm",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m ∧
  (q0' ≠ qf) ∧
   (ID (newm' m (q0',x0,qf)))^* (q,i,s) (q',i',s') ∧
   q' ∈ states m ∧
   q ∈ states m
        ⇒
    (ID m)^* (q,i,s) (q',i',s')``,

Q_TAC SUFF_TAC 
  `∀x y. (ID (newm' m (q0',x0,qf)))^* x y ⇒
         x0 ∉ stkSyms m ⇒
         q0' ∉ states m ⇒
         qf ∉ states m ⇒
         (q0' ≠ qf) ⇒
         ∀q s0 stk q' s1 stk'.
            (x = (q,s0,stk)) ∧ (y = (q',s1,stk')) ∧
             q' ∈ states m ∧ q ∈ (states m)
                   ⇒
        	(ID m)^* (q,s0,stk) (q',s1,stk')` THEN1 
METIS_TAC [] THEN 
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [RTC_RULES] THEN
Cases_on `x'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`q'' ∈ states m ∨ (q'' = qf)` by METIS_TAC [idStatesMem']
THENL[
      `∃l.ID (newm' m (q0',x0,qf)) ⊢ l ◁ 
                          (q'',q''',r') → (q',s1,stk')`
	    by METIS_TAC [rtc2list_exists'] THEN
      `q'' ∈ states m` by METIS_TAC [idStatesMem'] THEN
      METIS_TAC [RTC_RULES, idNewm'ImpOldm],


      SRW_TAC [][] THEN
      `∃l.ID (newm' m (q0',x0,q'')) ⊢ l ◁ 
                          (q'',q''',r') → (q',s1,stk')`
	    by METIS_TAC [rtc2list_exists'] THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
      SRW_TAC [][] THEN1 METIS_TAC [] THEN
      Cases_on `u` THEN Cases_on `r` THEN
      METIS_TAC [idcNewm'EndSt]]);



val idNewm'FstStep = store_thm
("idNewm'FstStep",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m ∧
  q0' ≠ qf ∧
  newm' m (q0',x0,qf) ⊢ (q0',i,[x0]) → (q,q'',r')
         ⇒
    (q = m.start) ∧ (q'' = i) ∧ (r' = m.ssSym::[x0])``,

Cases_on `i` THEN
SRW_TAC [][ID] THEN
FULL_SIMP_TAC (srw_ss()) [newm', LET_THM] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],
      
      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in]
      ]);


val newm'start = store_thm
("newm'start",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m  
          ⇒
    ((newm' m (q0',x0,qf)).start=q0')``,
SRW_TAC [][newm', LET_THM]);

val newm'ssSym = store_thm
("newm'ssSym",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m  
          ⇒
    ((newm' m (q0',x0,qf)).ssSym=x0)``,
SRW_TAC [][newm', LET_THM]);


val newm'toFs = store_thm
("newm'toFs",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m  ∧
  newm' m (q0',x0,qf) ⊢ (q,i,s) → (qf,i',s')
          ⇒
     (i=i') ∧ (s'= TL s)``,
SRW_TAC [][newm', LET_THM] THEN
Cases_on `i` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN 
METIS_TAC [notSomeInpMemFst', toStEqFs, APPEND]);


val toFsFromOldSt = store_thm
("toFsFromOldSt",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m  ∧
  newm' m (q0',x0,qf) ⊢ (q,i,s) → (qf,i',s')
          ⇒
     q ∈ states m``,
SRW_TAC [][newm', LET_THM] THEN
Cases_on `i` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [ID] 
THENL[

  FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

  FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

  METIS_TAC [memFslFst', mem_in, states_list_eqresult],

  FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

  METIS_TAC [notSomeInpMemFst'],

  FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

  FULL_SIMP_TAC (srw_ss()) [states] THEN METIS_TAC [],

  METIS_TAC [memFslFst', mem_in, states_list_eqresult]
  ]);



val fsTransPfxNil = store_thm
("fsTransPfxNil",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m  ∧
  ¬MEM x0 p' ∧
  newm' m (q0',x0,qf) ⊢ (q,i,p' ++ [x0]) → (qf,i',stk)
          ⇒
     (p'=[]) ∧ (stk=[])``,

Cases_on `i` THEN Cases_on `p'` THEN
SRW_TAC [][newm', LET_THM, ID] THEN
FULL_SIMP_TAC (srw_ss()) [states] THEN 
METIS_TAC [toStEqFs, notSomeInpMemFst']);

val lafsImpLaes' = store_thm
("lafsImpLaes'",
``x0 ∉ stkSyms m ∧
  q0' ∉ states m ∧
  qf ∉ states m ∧
  (q0' ≠ qf)
     ⇒
   (x ∈ lafs (newm' m (q0',x0,qf)) ⇒ x ∈ laes m)``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lafs, laes, IDC] THEN
`state=qf` by FULL_SIMP_TAC (srw_ss()) [newm', LET_THM] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(newm' m (q0',x0,qf)).ssSym=x0` by METIS_TAC [newm'ssSym] THEN
`(newm' m (q0',x0,qf)).start=q0'` by METIS_TAC [newm'start] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`((q0',x,[x0])=(qf,[],stack)) ∨
 ∃u.ID (newm' m (q0',x0,qf)) (q0',x,[x0]) u ∧
    (ID (newm' m (q0',x0,qf)))^* u (qf,[],stack)` 
    by METIS_TAC [RTC_CASES1] THEN
SRW_TAC [][] THEN
Cases_on `u`THEN Cases_on `r` THEN
`(q = m.start) ∧ (q' = x) ∧ (r' = [m.ssSym; x0])` 
	 by METIS_TAC [idNewm'FstStep] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss())  [Once RTC_CASES2] THEN
SRW_TAC [][] THEN1 FULL_SIMP_TAC (srw_ss()) [states] THEN
Cases_on `u'` THEN Cases_on `r` THEN
`(q''=[])` by METIS_TAC [newm'toFs] THEN
`q ∈ states m`  by METIS_TAC [toFsFromOldSt] THEN
`m.start ∈ states m` by FULL_SIMP_TAC (srw_ss()) [states] THEN
`(ID m)^* (m.start,q',[m.ssSym; x0]) (q,q'',r')` 
    by METIS_TAC [idcNewm'ImpOldm] THEN
IMP_RES_TAC idcStkPop THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`[m.ssSym]`] MP_TAC) THEN
SRW_TAC [][] THEN
`x0 ≠ m.ssSym` by FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃l. ID m ⊢ l ◁ (m.start,q',[m.ssSym; x0]) → (q,[],r')` 
    by METIS_TAC [rtc2list_exists'] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`r'`, `[]`, `q`, `m.start`,`l`,
			     `[]`,`q'`] MP_TAC) THEN
SRW_TAC [][] THEN
`(p'=[]) ∧ (stack=[])` by METIS_TAC [fsTransPfxNil] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
`l' ≠ []` by (Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
`(ID m)^* (m.start,q',[m.ssSym]) (q,[],[])` 
    by METIS_TAC [rtc2listRtcHdLast] THEN
`(m.start,q',[m.ssSym]) ≠ (q,[],[])` by SRW_TAC [][] THEN
METIS_TAC [RTC_CASES2]);



val thm5_2 = store_thm
("thm5_2",
``INFINITE (SYMUNIV : 'ssym set) ∧ INFINITE (STUNIV : 'state set) 
     ⇒
   ∀m.∃m'.laes (m:('isym, 'ssym, 'state) pda) = 
          lafs (m':('isym, 'ssym, 'state) pda)``,
SRW_TAC [] [EQ_IMP_THM, EXTENSION] THEN
`FINITE (stkSyms m)` 
     by METIS_TAC [finiteStkSyms, FINITE_LIST_TO_SET] THEN
`∃x0.x0 IN SYMUNIV ∧ x0 ∉ stkSyms m` 
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_ssym_exists] THEN
`FINITE (states m)` 
     by METIS_TAC [finiteStates, FINITE_LIST_TO_SET] THEN
`∃q0'.q0' IN STUNIV ∧ q0' ∉ states m` 
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists] THEN
`∃qf.qf IN STUNIV ∧ qf ∉ states m ∧ (qf ≠ q0')` 
    by MAGIC
(* METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists]*) THEN
Q.EXISTS_TAC `newm' m (q0',x0,qf)` THEN
SRW_TAC [][] THEN
METIS_TAC [laesImpLafs', lafsImpLaes']);

