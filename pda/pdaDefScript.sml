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


val pdastk = Define `pdastk (state,inp,stk) = stk`;
val pdainp = Define `pdainp (state,inp,stk) = inp`;
val pdastate = Define `pdastate (state,inp,stk) = state`;


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



val statesListApp = store_thm
("statesListApp",
``∀p1 p2.statesList' (p1++p2) =
           statesList' p1 ++ statesList' p2``,

Induct_on `p1` THEN Induct_on `p2` THEN
SRW_TAC [][statesList'] THEN
Cases_on `h'` THEN Cases_on `r`THEN
Cases_on `q` THEN Cases_on `r` THEN
SRW_TAC [][statesList']);


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

val _ = add_rule {
   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
   fixity = Infix(NONASSOC, 550),
   paren_style = OnlyIfNecessary,
   pp_elements = [BreakSpace(1,1), TOK "⊢",
		  BreakSpace(1,2),
                  BeginFinalBlock(PP.INCONSISTENT, 2),
                  TM, HardSpace 1, TOK "→*", BreakSpace(1,2)],
                  term_name = "IDC"};

val _ = overload_on ("IDC", ``\p. RTC (ID p)``);


val lafs = Define
`lafs (p:('isym, 'ssym, 'state) pda) =
              { w | ?state stack.
                IDC p (p.start,w,[p.ssSym]) (state,[],stack) ∧
                MEM state (p.final) }`;

val laes = Define
`laes (p:('isym, 'ssym, 'state) pda) =
              { w | ?state.
                    IDC p (p.start,w,[p.ssSym]) (state,[],[]) }`;



val stkLen = Define `stkLen e = LENGTH (pdastk e)`;


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

val idStkPop = store_thm
("idStkPop",
``∀q i p sym s q' i' stk'.
   m ⊢ (q,i,p ++ [sym] ++ s) → (q',i',stk') ∧
  ¬MEM sym p ∧
  ¬(sym ∈ stkSyms m)
        ⇒
    ∃p'.(stk' = p' ++ [sym] ++ s) ∧ ¬MEM sym p' ∧
         m ⊢ (q,i,p) → (q',i',p')``,
Cases_on `i` THEN Cases_on `p` THEN
SRW_TAC [][ID]
THENL[
      Cases_on `sym ∈ stkSyms m` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
      METIS_TAC [],


      Q.EXISTS_TAC `sl++t` THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
      METIS_TAC [mem_in],

      SPOSE_NOT_THEN ASSUME_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
      METIS_TAC [],

      FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
      METIS_TAC [mem_in],

      FULL_SIMP_TAC (srw_ss()) [stkSyms] THEN
      METIS_TAC [mem_in]
      ]);



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

		  `∃e.LAST (h::h'::t') = e`
		      by METIS_TAC [last_exists] THEN
		  Cases_on `e` THEN
		  Cases_on `r` THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN [`q`, `i`,`s`,
					       `q''`, `q'''`,`r'`,
					       `p`]
				MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
		  SRW_TAC [][] THEN
		  `rtc2list (ID m) (h'::t')`
		      by METIS_TAC [rtc2list_distrib_append_fst,
				    NOT_CONS_NIL,
				    APPEND_ASSOC, APPEND] THEN
		  `∃l' p'.(r' = p' ++ [sym] ++ s) ∧ ¬MEM sym p' ∧
                          rtc2list (ID m) l' ∧ (HD l' = (q,i,p)) ∧
                          (LAST l' = (q'',q''',p'))`
		      by METIS_TAC [] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `h'::t' = FRONT (h'::t') ++
				  [(q'',q''',p' ++ [sym] ++ s)]`
		      by METIS_TAC [APPEND_FRONT_LAST,
				    NOT_CONS_NIL] THEN
		  `rtc2list (ID m) (FRONT (h'::t') ++
				  [(q'',q''',p' ++ [sym] ++ s)] ++
				  [x])` by METIS_TAC [APPEND_ASSOC,
						      APPEND] THEN
		  `rtc2list (ID m) ([(q'',q''',p' ++ [sym] ++ s)]
					++ [x])`
		      by METIS_TAC [APPEND_ASSOC,
				    rtc2list_distrib_append_snd,
				    MEM, MEM_APPEND] THEN
		  `x=(q',i',stk')`
		      by METIS_TAC [LAST_DEF, NOT_CONS_NIL,
				    last_append, APPEND,
				    APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  `∃p''.(stk' = p'' ++ [sym] ++ s) ∧ ¬MEM sym p'' ∧
				 m ⊢ (q'',q''',p') → (q',i',p'')`
		      by METIS_TAC [idStkPop] THEN
		  Q.EXISTS_TAC `l'++[(q',i',p'')]` THEN
		  Q.EXISTS_TAC `p''` THEN
		  SRW_TAC [][]
		  THENL[

			METIS_TAC [rtc2list_append_right],

			Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) [],

			METIS_TAC [last_append, NOT_CONS_NIL, LAST_DEF]
			]]]]);


val idInpInsert = store_thm
("idInpInsert",
``m ⊢ (q,x,stk) → (q',x',stk')
      ⇒
   ∀l.m ⊢ (q,x++l,stk) → (q',x'++l,stk')``,

SRW_TAC [][] THEN
Cases_on `x` THEN
Cases_on `l` THEN
Cases_on `stk` THEN
FULL_SIMP_TAC (srw_ss()) [ID]);


val idcInpInsert = store_thm
("idcInpInsert",
``(ID m)^* (q,x,stk) (q',x',stk')
      ⇒
   ∀l.(ID m)^* (q,x++l,stk) (q',x'++l,stk')``,

Q_TAC SUFF_TAC
  `!x y. (ID m)^* x y ==>
         !q s0 stk q' s1 stk'.
            (x = (q,s0,stk)) ∧ (y = (q',s1,stk')) ⇒
            ∀l. (ID m)^* (q,s0++l,stk) (q',s1++l,stk')`
  THEN1 METIS_TAC [] THEN
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
METIS_TAC [idInpInsert, TypeBase.nchotomy_of ``:'a # 'b``,
	   RTC_RULES]);



val id_thm = store_thm
("id_thm",
``p ⊢ (q0,i0,s0) → (q,i,s) ⇔
(∃sh st st'. (s0 = sh::st) ∧ MEM ((NONE,sh,q0),q,st') p.next ∧
 (s=st'++st) ∧ (i=i0))
∨
∃sh st st' ih. (s0 = sh::st) ∧ MEM ((SOME ih,sh,q0),q,st') p.next ∧
 (s=st'++st) ∧ (i0=ih::i)``,

Cases_on `i0` THEN Cases_on `s0` THEN SRW_TAC [][ID] THEN
METIS_TAC []);


val ldIdcInpLen = store_thm
("ldIdcInpLen",
``∀q q' i i' s s'.
   (ID p) ⊢ dl ◁ (q,i,s) → (q',i',s')
     ⇒
   (LENGTH i' ≤ LENGTH i)``,

Induct_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm, listderiv_def] THEN
SRW_TAC [][] THEN
 DECIDE_TAC);


val pdaTransOnPfx = store_thm
("pdaTransOnPfx",
``∀q q' ipfx isfx spfx ssfx.
   ID p ⊢ dl ◁ (q,ipfx++isfx,spfx++ssfx) → (q',isfx,ssfx) ⇒
   (∀e.MEM e (FRONT dl) ⇒ ∃p.(p ≠ []) ∧ (pdastk e = p++ssfx))
      ⇒
      (ID p)^* (q,ipfx,spfx) (q',[],[])``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`(dl=[]) ∨ ∃q1 i1 s1 dl'.dl=(q1,i1,s1)::dl'` by
 (Cases_on `dl` THEN SRW_TAC [][] THEN
  Cases_on `h` THEN Cases_on `r` THEN SRW_TAC [][]) THEN
SRW_TAC [][] THEN1
 FULL_SIMP_TAC (srw_ss()) [APPEND_EQ_SELF] THEN
`(dl'=[]) ∨ (∃q2 i2 s2 dl2.dl'=(q2,i2,s2)::dl2)` by
(Cases_on `dl'` THEN SRW_TAC [][] THEN Cases_on `h` THEN Cases_on `r` THEN
SRW_TAC [][]) THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [pdastk] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][]
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [APPEND_EQ_SELF] THEN
	    `(st'=[]) ∧ (spfx=[sh])` by
	    (`LENGTH (spfx++st'++st) = LENGTH (sh::st)` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `LENGTH spfx + LENGTH st' = 1` by DECIDE_TAC THEN
 	     `LENGTH spfx ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
	     `LENGTH st' = 0` by DECIDE_TAC THEN
	     `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [APPEND, APPEND_11]) THEN
	    SRW_TAC [][] THEN
	    MATCH_MP_TAC RTC_SUBSET THEN
	    SRW_TAC [][id_thm],


	    `ipfx=[ih]` by METIS_TAC [APPEND, APPEND_11] THEN
	    SRW_TAC [][] THEN
	    `(st'=[]) ∧ (spfx=[sh])` by
	    (`LENGTH (spfx++st'++st) = LENGTH (sh::st)` by METIS_TAC [APPEND_ASSOC] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `LENGTH spfx + LENGTH st' = 1` by DECIDE_TAC THEN
 	     `LENGTH spfx ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
	     `LENGTH st' = 0` by DECIDE_TAC THEN
	     `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [APPEND, APPEND_11]) THEN
	    SRW_TAC [][] THEN
	    MATCH_MP_TAC RTC_SUBSET THEN
	    SRW_TAC [][id_thm]
	    ],


      FULL_SIMP_TAC (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM, pdastk] THEN
      SRW_TAC [][] THEN
      ONCE_REWRITE_TAC [RTC_CASES1] THEN
      DISJ2_TAC THEN
      Q.PAT_ASSUM `X ⊢ (q,Y,Z) → WW` MP_TAC THEN
      SRW_TAC [][id_thm]
      THENL[
	    Q.EXISTS_TAC `(q1,ipfx,p')` THEN
	    Cases_on `spfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `p'=st'++t` by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
	    SRW_TAC [][id_thm],

	    `LENGTH isfx <= LENGTH i2` by METIS_TAC [listderiv_def, ldIdcInpLen,
						     rtc2listRtcHdLast, HD] THEN

	    `LENGTH i2 <= LENGTH i1` by METIS_TAC [ldIdcInpLen, IDC,RTC_SUBSET,
						   rtc2list_exists'] THEN
	    `LENGTH isfx <= LENGTH i1` by DECIDE_TAC THEN
	    Cases_on `ipfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	    (`LENGTH isfx = LENGTH (ih::i1)` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `spfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
 	    Q.EXISTS_TAC `(q1,t,st'++t')` THEN
 	    SRW_TAC [][id_thm] THEN
	    `p'=st'++t'` by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
	    SRW_TAC [][id_thm]
	    ]]);


val ldIdcInpSuffix = store_thm
("ldIdcInpSuffix",
``∀q q' inp inp' stk stk'.
  (ID p) ⊢ dl ◁ (q,inp,stk) → (q',inp',stk')
      ⇒
    ∃p.(inp=p++inp') ∧ isSuffix inp' inp``,

 Induct_on `dl` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN1 METIS_TAC [APPEND_NIL] THEN
 Cases_on `h` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
 Q.EXISTS_TAC `ih::p'` THEN
SRW_TAC [][isSuffix_def, REVERSE_APPEND, IS_PREFIX_APPEND] THEN
METIS_TAC [APPEND_ASSOC]);



val frontdlProp = store_thm
("frontdlProp",
``∀q q' r rst r' h.
   ID p ⊢ dl ◁ (q,[],[h]++rst) → (q',[],r'++rst) ⇒
   (∀e.MEM e dl ⇒ LENGTH ([h]++rst) ≤ LENGTH (pdastk e))
   ⇒
   (∀e.MEM e dl ⇒ ∃p.(p ≠ []) ∧ (pdastk e = p++rst))``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND,NOT_CONS_NIL,pdastk] THEN1
METIS_TAC [APPEND,NOT_CONS_NIL,pdastk] THEN1
(Cases_on `e`  THEN
 Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [pdastk] THEN
 `1 + LENGTH rst ≤ LENGTH (st'++rst)` by METIS_TAC [pdastk] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 `LENGTH st' ≠ 0` by DECIDE_TAC THEN
 METIS_TAC [LENGTH_NIL]) THEN
`t' ≠ []` by METIS_TAC [MEM] THEN
`MEM e ((FRONT t')++[LAST t'])` by METIS_TAC [APPEND_FRONT_LAST] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[

(* MEM e FRONT t' *)

`LENGTH (FRONT t') < LENGTH t'` by METIS_TAC [frontLen] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((q,[],h::rst)::h''::FRONT t')`]
	       MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`((q,[],h::rst)::h''::FRONT t')`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `h''`  THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [pdastk] THEN
`1 + LENGTH rst ≤ LENGTH (st'++rst)` by METIS_TAC [pdastk] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH st' ≠ 0` by DECIDE_TAC THEN
Cases_on `st'` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`FRONT t'≠[]` by METIS_TAC [MEM] THEN
`LAST t' = (q',[],r' ++ rst)` by METIS_TAC [last_append,APPEND,MEM,
					    MEM_APPEND,APPEND_ASSOC] THEN
`rtc2list (ID p) ([LAST (FRONT t')]++[(q',[],r' ++ rst)])`
by METIS_TAC [rtc2listLastFront,rtc2list_distrib_append_snd,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
Cases_on `LAST (FRONT t')` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][]
THENL[
      IMP_RES_TAC twoListAppEq THEN
      SRW_TAC [][]
      THENL[
	    FIRST_X_ASSUM (Q.SPECL_THEN [`q'''`,`[sh]`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `rtc2list (ID p) ((q'',[],h'::(t ++ rst))::FRONT t')`
	    by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
			  APPEND_ASSOC,APPEND_FRONT_LAST] THEN
	    `(LAST ((q'',[],h'::(t ++ rst))::FRONT t') =
            (q''',[],sh::rst))` by METIS_TAC [last_append,NOT_CONS_NIL,
					      APPEND] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`q'''`,`sh::s1'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `rtc2list (ID p) ((q'',[],h'::(t ++ rst))::FRONT t')`
	    by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
			  APPEND_ASSOC,APPEND_FRONT_LAST] THEN
	    `(LAST ((q'',[],h'::(t ++ rst))::FRONT t') =
            (q''',[],sh::(s1'++rst)))` by METIS_TAC [last_append,
						   NOT_CONS_NIL,APPEND] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST],


	    `MEM (q''',[],sh::s2) t'` by METIS_TAC [APPEND_FRONT_LAST,
						    MEM,MEM_APPEND] THEN
	    `1 + LENGTH (s1 ++ s2) ≤ LENGTH (sh::s2)`
	    by METIS_TAC [pdastk] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `LENGTH s1=0`by DECIDE_TAC THEN
	    `s1=[]` by METIS_TAC [LENGTH_NIL] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`q'''`,`[sh]`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `rtc2list (ID p) ((q'',[],h'::(t ++ s2))::FRONT t')`
	    by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
			  APPEND_ASSOC,APPEND_FRONT_LAST] THEN
	    `(LAST ((q'',[],h'::(t ++ s2))::FRONT t') =
            (q''',[],sh::s2))` by METIS_TAC [last_append,
					     NOT_CONS_NIL,APPEND] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,NOT_CONS_NIL]
	    ],


      `rtc2list (ID p) ((q'',[],h'::(t ++ rst))::FRONT t')`
      by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
		    APPEND_ASSOC,APPEND_FRONT_LAST] THEN
      `ID p ⊢ ((q'',[],h'::(t ++ rst))::FRONT t') ◁
           (q'',[],h'::(t++rst)) → (q''',[ih],sh::st) ⇒
         ∃p. ([] = p ++ [ih]) ∧ isSuffix [ih] []`
      by METIS_TAC [ldIdcInpSuffix] THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `(LAST ((q'',[],h'::(t ++ rst))::FRONT t') =
	 (q''',[ih],sh::st))` by METIS_TAC [last_append,
					  NOT_CONS_NIL,APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) []
      ],


(* e = LAST t' *)


`r'≠[]` by
(SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 `1 + LENGTH rst ≤ LENGTH rst` by METIS_TAC [pdastk,last_append,
					     APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (arith_ss) []) THEN
METIS_TAC [last_append,NOT_CONS_NIL,pdastk,APPEND]
]);



val frontdlPropGen = store_thm
("frontdlPropGen",
``∀q i0 isfx r0 rst q' i' isfx r' rst.
   ID p ⊢ dl ◁ (q,i0++isfx,r0++rst) → (q',i'++isfx,r'++rst) ⇒ (r0≠[]) ⇒
   (∀e.MEM e dl ⇒ LENGTH (r0++rst) ≤ LENGTH (pdastk e))
      ⇒
   (∀e.MEM e dl ⇒ ∃p.(p ≠ []) ∧ (pdastk e = p++rst))``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND,NOT_CONS_NIL,pdastk] THEN1
METIS_TAC [APPEND,NOT_CONS_NIL,pdastk] THEN1
(Cases_on `e`  THEN
 Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [pdastk] THEN
 (`LENGTH r0 + LENGTH rst ≤ LENGTH (st'++st)` by METIS_TAC [pdastk] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
 `LENGTH st' ≠ 0` by DECIDE_TAC THEN
 METIS_TAC [LENGTH_NIL])) THEN
`t' ≠ []` by METIS_TAC [MEM] THEN
`MEM e ((FRONT t')++[LAST t'])` by METIS_TAC [APPEND_FRONT_LAST] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[

(* MEM e FRONT t' *)

`LENGTH (FRONT t') < LENGTH t'` by METIS_TAC [frontLen] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH((q,i0++isfx,r0++rst)::h'::FRONT t')`]
	       MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`((q,i0 ++ isfx,r0 ++ rst)::h'::FRONT t')`]
	       MP_TAC) THEN
SRW_TAC [][] THEN
`FRONT t'≠[]` by METIS_TAC [MEM] THEN
`LAST t' = (q',i'++isfx,r' ++ rst)` by METIS_TAC [APPEND,last_append,
						  APPEND_ASSOC,MEM,
						  MEM_APPEND] THEN
`rtc2list (ID p) ([LAST (FRONT t')]++[(q',i'++isfx,r' ++ rst)])`
by METIS_TAC [rtc2listLastFront,rtc2list_distrib_append_snd,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `LAST (FRONT t')` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][]
THENL[
      IMP_RES_TAC twoListAppEq THEN
      SRW_TAC [][]
      THENL[
	    `rtc2list (ID p) (h'::FRONT t')`
	    by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
			  APPEND_ASSOC,APPEND_FRONT_LAST] THEN

	    `(LAST (h'::FRONT t') =
            (q'',i'++isfx,[sh]++rst))` by METIS_TAC [last_append,NOT_CONS_NIL,
					      APPEND] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`i0`,`r0`,`q''`,`i'`,`isfx`,
					 `[sh]`,`rst`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `(∀e'.
              (e' = (q,i0 ++ isfx,r0 ++ rst)) ∨ (e' = h') ∨
              MEM e' (FRONT t') ⇒
              LENGTH r0 + LENGTH rst ≤ LENGTH (pdastk e'))`
	    by METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,MEM] THEN
	    METIS_TAC [],


	    `rtc2list (ID p) (h'::FRONT t')`
	    by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
			  APPEND_ASSOC,APPEND_FRONT_LAST] THEN
	    `(LAST (h'::FRONT t') =
            (q'',i'++isfx,[sh]++(s1'++rst)))` by METIS_TAC [last_append,
							    NOT_CONS_NIL,
							    APPEND] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`i0`,`r0`,`q''`,`i'`,`isfx`,
					 `[sh]++s1'`,`rst`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,MEM],


	    `rtc2list (ID p) (h'::FRONT t')`
	    by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
			  APPEND_ASSOC,APPEND_FRONT_LAST] THEN
	    `(LAST (h'::FRONT t') =
            (q'',i'++isfx,[sh]++s2))` by METIS_TAC [last_append,
						    NOT_CONS_NIL,
						    APPEND] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`i0`,`r0`,`q''`,`i'`,`isfx`,
					 `[sh]`,`s2`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `MEM (q'',i'++isfx,sh::s2) t'`
	    by METIS_TAC [APPEND_FRONT_LAST,
			  MEM,MEM_APPEND] THEN
	    `LENGTH r0 + LENGTH (s1 ++ s2) ≤ LENGTH (sh::s2)`
	    by METIS_TAC [pdastk] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `r0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    `LENGTH s1=0`by DECIDE_TAC THEN
	    `s1=[]` by METIS_TAC [LENGTH_NIL] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,MEM]
 	    ],


      `rtc2list (ID p) (h'::FRONT t')`
      by METIS_TAC [rtc2list_distrib_append_fst,APPEND,NOT_CONS_NIL,
		    APPEND_ASSOC,APPEND_FRONT_LAST] THEN
      IMP_RES_TAC twoListAppEq THEN
      SRW_TAC [][]
      THENL[
	    `(LAST (h'::FRONT t') =
            (q'',ih::(i'++isfx),[sh]++rst))` by METIS_TAC [last_append,
						     NOT_CONS_NIL,
						     APPEND] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`i0`,`r0`,`q''`,`ih::i'`,`isfx`,
					 `[sh]`,`rst`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `(∀e'.
              (e' = (q,i0 ++ isfx,r0 ++ rst)) ∨ (e' = h') ∨
              MEM e' (FRONT t') ⇒
              LENGTH r0 + LENGTH rst ≤ LENGTH (pdastk e'))`
	    by METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,MEM] THEN
	    METIS_TAC [],

	    `(LAST (h'::FRONT t') =
            (q'',ih::(i'++isfx),[sh]++(s1'++rst)))`
	    by METIS_TAC [last_append,NOT_CONS_NIL,APPEND] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`i0`,`r0`,`q''`,`ih::i'`,`isfx`,
					 `[sh]++s1'`,`rst`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,MEM],


	    `(LAST (h'::FRONT t') =
            (q'',ih::(i'++isfx),[sh]++s2))` by METIS_TAC [last_append,
						    NOT_CONS_NIL,
						    APPEND] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`i0`,`r0`,`q''`,`ih::i'`,`isfx`,
					 `[sh]`,`s2`]
			   MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `MEM (q'',ih::(i'++isfx),sh::s2) t'`
	    by METIS_TAC [APPEND_FRONT_LAST,
			  MEM,MEM_APPEND] THEN
	    `LENGTH r0 + LENGTH (s1 ++ s2) ≤ LENGTH (sh::s2)`
	    by METIS_TAC [pdastk] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `r0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    `LENGTH s1=0`by DECIDE_TAC THEN
	    `s1=[]` by METIS_TAC [LENGTH_NIL] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [MEM_APPEND,APPEND_FRONT_LAST,MEM]
	    ]],


(* e = LAST t' *)

`r'≠[]` by
(SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 `LENGTH r0 + LENGTH rst ≤ LENGTH rst` by METIS_TAC [pdastk,last_append,
					     APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (arith_ss) [] THEN
`LENGTH r0 = 0` by DECIDE_TAC THEN
METIS_TAC [LENGTH_NIL]) THEN
METIS_TAC [last_append,NOT_CONS_NIL,pdastk,APPEND]
]);


val dlprop = store_thm
("dlprop",
``∀dl q q' h rst.
   ID p ⊢ dl ◁ (q,[],h::rst) → (q',[],rst) ⇒
   (∀e.MEM e (FRONT dl) ⇒ LENGTH (h::rst) ≤ LENGTH (pdastk e))
      ⇒
   (∀e.MEM e (FRONT dl) ⇒ ∃p.(p ≠ []) ∧ (pdastk e = p++rst))``,

 SRW_TAC [][] THEN
 `FRONT dl ≠ []` by METIS_TAC [MEM] THEN
 Cases_on `dl=[]` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 `dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`FRONT dl = FRONT(FRONT dl)++[LAST (FRONT dl)]`
 by METIS_TAC [APPEND_FRONT_LAST] THEN
 `ID p (LAST (FRONT dl)) (q',[],rst)`
by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
    SRW_TAC [][] THEN
    `rtc2list (ID p) ([(LAST (FRONT dl))]++[(q',[],rst)])`
    by METIS_TAC [rtc2list_distrib_append_snd,APPEND_ASSOC,MEM,
		  MEM_APPEND] THEN
    FULL_SIMP_TAC (srw_ss()) []) THEN
 Cases_on `LAST (FRONT dl)` THEN
Cases_on `r`  THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) []
THENL[

      `MEM (q'',[],sh::st) (FRONT dl)` by METIS_TAC [APPEND_FRONT_LAST,
						     MEM,MEM_APPEND] THEN
      `SUC (LENGTH st' + LENGTH st) ≤ LENGTH (sh::st)`
      by METIS_TAC [pdastk] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH st'=0` by DECIDE_TAC THEN
      `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `ID p ⊢ FRONT dl ◁ (q,[],[h]++st) → (q'',[],[sh] ++ st)`
      by METIS_TAC [listderivfront,APPEND] THEN
      `LENGTH ([h]++st) = SUC (LENGTH st)`
      by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      METIS_TAC [frontdlProp],

      `ID p ⊢ FRONT dl ◁ (q,[],h::(st'++st)) → (q'',[ih],[sh] ++ st)`
      by METIS_TAC [listderivfront,APPEND] THEN
      IMP_RES_TAC ldIdcInpSuffix THEN
      FULL_SIMP_TAC (srw_ss()) []]);


val dlpropGen = store_thm
("dlpropGen",
``∀q i0 isfx r0 rst q' i' isfx r' rst.
   ID p ⊢ dl ◁ (q,i0++isfx,r0++rst) → (q',i'++isfx,r'++rst) ⇒ (r0≠[]) ⇒
   (∀e.MEM e (FRONT dl) ⇒ LENGTH (r0++rst) ≤ LENGTH (pdastk e))
      ⇒
   (∀e.MEM e (FRONT dl) ⇒ ∃p.(p ≠ []) ∧ (pdastk e = p++rst))``,

 SRW_TAC [][] THEN
 `FRONT dl ≠ []` by METIS_TAC [MEM] THEN
 Cases_on `dl=[]` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 `dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`FRONT dl = FRONT(FRONT dl)++[LAST (FRONT dl)]`
 by METIS_TAC [APPEND_FRONT_LAST] THEN
 `ID p (LAST (FRONT dl)) (q',i' ++ isfx,r' ++ rst)`
by (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
    SRW_TAC [][] THEN
    `rtc2list (ID p) ([(LAST (FRONT dl))]++[(q',i' ++ isfx,r' ++ rst)])`
    by METIS_TAC [rtc2list_distrib_append_snd,APPEND_ASSOC,MEM,
		  MEM_APPEND] THEN
    FULL_SIMP_TAC (srw_ss()) []) THEN
 Cases_on `LAST (FRONT dl)` THEN
Cases_on `r`  THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) []
THENL[

      `MEM (q'',i'++isfx,sh::st) (FRONT dl)`
      by METIS_TAC [APPEND_FRONT_LAST,MEM,MEM_APPEND] THEN
      `LENGTH r0 + LENGTH rst ≤ LENGTH (sh::st)`
      by METIS_TAC [pdastk] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `r0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN
      SRW_TAC [][]
      THENL[
	    `LENGTH t = 0` by DECIDE_TAC THEN
	    `t=[]` by METIS_TAC [LENGTH_NIL] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `ID p ⊢ FRONT dl ◁ (q,i0 ++ isfx,[h] ++ rst)
	    → (q'',i' ++ isfx,[sh]++rst)`
	    by METIS_TAC [listderivfront,APPEND] THEN
	    `LENGTH ([h]++rst) = LENGTH rst+1`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC frontdlPropGen THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `ID p ⊢ FRONT dl ◁ (q,i0 ++ isfx,(h::t) ++ rst)
	    → (q'',i' ++ isfx,(sh::s1')++rst)`
	    by METIS_TAC [listderivfront,APPEND] THEN
	    `LENGTH (h::t ++ rst) = SUC (LENGTH t) + LENGTH rst`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC frontdlPropGen THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `(LENGTH s1 = 0) ∧ (LENGTH t = 0)` by DECIDE_TAC THEN
	    `(s1=[]) ∧ (t=[])`  by METIS_TAC [LENGTH_NIL] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `ID p ⊢ FRONT dl ◁ (q,i0 ++ isfx,[h] ++ s2)
	    → (q'',i' ++ isfx,[sh]++s2)`
	    by METIS_TAC [listderivfront,APPEND] THEN
	    `LENGTH ([h] ++ s2) = LENGTH s2 +1`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC frontdlPropGen THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    ],

      `MEM (q'',ih::(i'++isfx),sh::st) (FRONT dl)`
      by METIS_TAC [APPEND_FRONT_LAST,MEM,MEM_APPEND] THEN
      `LENGTH r0 + LENGTH rst ≤ LENGTH (sh::st)`
      by METIS_TAC [pdastk] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `r0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN
      SRW_TAC [][]
      THENL[
	    `LENGTH t = 0` by DECIDE_TAC THEN
	    `t=[]` by METIS_TAC [LENGTH_NIL] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `ID p ⊢ FRONT dl ◁ (q,i0 ++ isfx,[h] ++ rst)
	    → (q'',(ih::i') ++ isfx,[sh]++rst)`
	    by METIS_TAC [listderivfront,APPEND] THEN
	    `LENGTH ([h]++rst) = LENGTH rst+1`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC frontdlPropGen THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `ID p ⊢ FRONT dl ◁ (q,i0 ++ isfx,(h::t) ++ rst)
	    → (q'',(ih::i') ++ isfx,(sh::s1')++rst)`
	    by METIS_TAC [listderivfront,APPEND] THEN
	    `LENGTH (h::t ++ rst) = SUC (LENGTH t) + LENGTH rst`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC frontdlPropGen THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `(LENGTH s1 = 0) ∧ (LENGTH t = 0)` by DECIDE_TAC THEN
	    `(s1=[]) ∧ (t=[])`  by METIS_TAC [LENGTH_NIL] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `ID p ⊢ FRONT dl ◁ (q,i0 ++ isfx,[h] ++ s2)
	    → (q'',(ih::i') ++ isfx,[sh]++s2)`
	    by METIS_TAC [listderivfront,APPEND] THEN
	    `LENGTH ([h] ++ s2) = LENGTH s2 +1`
	    by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	    IMP_RES_TAC frontdlPropGen THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    ]]);




val pdaTransOnPfxLd = store_thm
("pdaTransOnPfxLd",
``∀q q' ipfx isfx spfx ssfx.
   ID p ⊢ dl ◁ (q,ipfx++isfx,spfx++ssfx) → (q',isfx,ssfx) ⇒
   (∀e.MEM e (FRONT dl) ⇒ ∃p.(p ≠ []) ∧ (pdastk e = p++ssfx))
      ⇒
      ∃l.LENGTH l ≤ LENGTH dl ∧
      ID p ⊢ l ◁ (q,ipfx,spfx) → (q',[],[])``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`(dl=[]) ∨ ∃q1 i1 s1 dl'.dl=(q1,i1,s1)::dl'` by
 (Cases_on `dl` THEN SRW_TAC [][] THEN
  Cases_on `h` THEN Cases_on `r` THEN SRW_TAC [][]) THEN
SRW_TAC [][] THEN1
 (FULL_SIMP_TAC (srw_ss()) [APPEND_EQ_SELF] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `[(q,[],[])]` THEN
SRW_TAC [][]) THEN
`(dl'=[]) ∨ (∃q2 i2 s2 dl2.dl'=(q2,i2,s2)::dl2)` by
(Cases_on `dl'` THEN SRW_TAC [][] THEN Cases_on `h` THEN Cases_on `r` THEN
SRW_TAC [][]) THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [pdastk] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][]
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [APPEND_EQ_SELF] THEN
	    `(st'=[]) ∧ (spfx=[sh])` by
	    (`LENGTH (spfx++st'++st) = LENGTH (sh::st)` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `LENGTH spfx + LENGTH st' = 1` by DECIDE_TAC THEN
 	     `LENGTH spfx ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
	     `LENGTH st' = 0` by DECIDE_TAC THEN
	     `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [APPEND, APPEND_11]) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Q.EXISTS_TAC `[(q,[],[sh]);(q',[],[])]` THEN
	    SRW_TAC [][id_thm],


	    `ipfx=[ih]` by METIS_TAC [APPEND, APPEND_11] THEN
	    SRW_TAC [][] THEN
	    `(st'=[]) ∧ (spfx=[sh])` by
	    (`LENGTH (spfx++st'++st) = LENGTH (sh::st)` by METIS_TAC [APPEND_ASSOC] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `LENGTH spfx + LENGTH st' = 1` by DECIDE_TAC THEN
 	     `LENGTH spfx ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
	     `LENGTH st' = 0` by DECIDE_TAC THEN
	     `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [APPEND, APPEND_11]) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Q.EXISTS_TAC `[(q,[ih],[sh]);(q',[],[])]` THEN
	    SRW_TAC [][id_thm]
	    ],

      FULL_SIMP_TAC (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM, pdastk] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][]
      THENL[
	    FIRST_X_ASSUM (Q.SPECL_THEN [`ipfx`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `spfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `(q,ipfx,h::t)::l` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (arith_ss) [] THEN
	    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][id_thm]  THEN
	    Q.EXISTS_TAC `st'` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND_ASSOC, APPEND_11],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`ipfx`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `spfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `(q,ipfx,h::t)::l` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (arith_ss) [] THEN
	    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][id_thm]  THEN
	    Q.EXISTS_TAC `st'` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND_ASSOC, APPEND_11],



	    `LENGTH isfx <= LENGTH i1` by METIS_TAC [listderiv_def, ldIdcInpLen,
						     rtc2listRtcHdLast, HD] THEN
	    Cases_on `ipfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	    (`LENGTH isfx = LENGTH (ih::i1)` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `spfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `(q,h::t,h'::t')::l` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (arith_ss) [] THEN
	    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][id_thm]  THEN
	    Q.EXISTS_TAC `st'` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND_ASSOC, APPEND_11],


	    `LENGTH isfx <= LENGTH i2` by METIS_TAC [listderiv_def, ldIdcInpLen,
						     rtc2listRtcHdLast, HD] THEN
 	    Cases_on `ipfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	    (`LENGTH isfx = LENGTH (ih::ih'::i2)` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `spfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`t`] MP_TAC) THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `(q,h::t,h'::t')::l` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (arith_ss) [] THEN
	    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][id_thm]  THEN
	    Q.EXISTS_TAC `st'` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND_ASSOC, APPEND_11]
	    ]]);




val stackRedGen = store_thm
("stackRedGen",
``(f (LAST l) = 0) ∧ l ≠ [] ∧
 (∀i.i+1 < LENGTH l ∧ (f (EL (i+1) l) < f (EL i l)) ⇒
 (f (EL i l) = f (EL (i+1) l) + 1))
   ⇒
  ∀n.n ≤ f (HD l) ⇒ ∃i.(f (EL i l) = n) ∧ (i < LENGTH l)
  ∧ ∀j.j < i ⇒ n < f (EL j l)``,

STRIP_TAC THEN Induct THEN
SRW_TAC [][]
THENL[

      Q.EXISTS_TAC `LEAST m. (f (EL m l) = 0) ∧ m < LENGTH l` THEN
      numLib.LEAST_ELIM_TAC THEN
      SRW_TAC [][DECIDE ``x ≠ 0 ⇔ 0 < x``] THENL [
        Q.EXISTS_TAC `PRE (LENGTH l)` THEN
        SRW_TAC [][EL_PRE_LENGTH] THEN
        Q_TAC SUFF_TAC `0 < LENGTH l` THEN1 DECIDE_TAC THEN
        METIS_TAC [DECIDE ``0 < x ⇔ (x ≠ 0)``, LENGTH_NIL],

        METIS_TAC [arithmeticTheory.LESS_TRANS]
      ],

      `n ≤ f (HD l)` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `i ≠ 0` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN DECIDE_TAC) THEN
      `f (EL (i-1) l) = SUC n`
        by (Q.PAT_ASSUM `∀x:num.P x` MP_TAC THEN
	    FIRST_X_ASSUM (Q.SPEC_THEN `i-1` MP_TAC) THEN
	    SRW_TAC [ARITH_ss][]) THEN
      Q.EXISTS_TAC `LEAST m. (f (EL m l) = SUC n) ∧ m < LENGTH l` THEN
      numLib.LEAST_ELIM_TAC THEN SRW_TAC [][]
      THENL [
	     Q.EXISTS_TAC `i-1` THEN SRW_TAC [][] THEN
	     DECIDE_TAC,

	     Cases_on `n'=i` THEN SRW_TAC [][] THEN
	     RES_TAC THEN
	     FULL_SIMP_TAC (arith_ss) [] THEN
	     `(n'>i) ∨ (n'<i)` by DECIDE_TAC THEN
	     FULL_SIMP_TAC (arith_ss) [] THEN
	     `j < i` by DECIDE_TAC THEN
	     RES_TAC THEN
	     FULL_SIMP_TAC (arith_ss) []
	     ]]);


open arithmeticTheory;
open markerTheory;

val ldIdcStkLen = store_thm
("ldIdcStkLen",
``∀l q inp s q' inp' s'.
 (ID p) ⊢ l ◁ (q,inp,s) → (q',inp',s')
  ⇒
 (∀i.i + 1 < LENGTH l ∧ stkLen (EL (i + 1) l) < stkLen (EL i l) ⇒
          (stkLen (EL i l) = stkLen (EL (i + 1) l) + 1))``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      DECIDE_TAC,

      Cases_on `h` THEN Cases_on `r` THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`q''`,`q'''`,`r'`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `ID p (EL i  ((q,inp,s)::(q'',q''',r')::t))
      (EL (i+1)  ((q,inp,s)::(q'',q''',r')::t))`
      by (`i+1 < LENGTH ((q,inp,s)::(q'',q''',r')::t)`
      by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      `rtc2list (ID p) ((q,inp,s)::(q'',q''',r')::t)`
      by FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
	  METIS_TAC [elId]) THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][]
      THENL[
	    Q.ABBREV_TAC `l = ((q,inp,sh::st)::(q'',inp,st' ++ st)::t)` THEN
	    Cases_on `EL i l` THEN Cases_on `r` THEN
	    Cases_on `EL (i+1) l` THEN Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [id_thm,stkLen,pdastk] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    DECIDE_TAC,

	    Q.ABBREV_TAC `l = ((q,ih::q''',sh::st)::(q'',q''',st' ++ st)::t)` THEN
	    Cases_on `EL i l` THEN Cases_on `r` THEN
	    Cases_on `EL (i+1) l` THEN Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [id_thm,stkLen,pdastk] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    DECIDE_TAC
	    ]]);



val idcInpSplit = store_thm
("idcInpSplit",
``∀q i s q' i' s'.
 (ID p) ⊢ dl ◁ (q,i,s) → (q',i',s')
    ⇒
   ∃ipfx.(i=ipfx++i')``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND_NIL] THEN
Cases_on `h` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND,APPEND_ASSOC]);


val rtc2listIdStkNil = store_thm
("rtc2listIdStkNil",
``rtc2list (ID p) ((q,i,[])::t) ⇒ (t=[])``,

Cases_on `t` THEN SRW_TAC [][] THEN
Cases_on `h` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm]);


val idcStkLastSplit = store_thm
("idcStkLastSplit",
``∀dl q i s q' i' s'.
 (ID p) ⊢ dl ◁ (q,i,s) → (q',i',s')
    ⇒
   (∀qx ix sx.MEM (qx,ix,sx) (FRONT dl) ⇒ (LENGTH s <= LENGTH sx))
    ⇒
    (s=[]) ∨ (∃p.(s'=p++TL s))``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND] THEN
Cases_on `dl=[]` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(Cases_on `s` THEN SRW_TAC [][] THEN
METIS_TAC [APPEND]) THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][],

      `t=FRONT t++[LAST t]` by METIS_TAC [APPEND_FRONT_LAST] THEN
       Cases_on `LAST t` THEN
       Cases_on `r` THEN
       `rtc2list (ID p) ((q,i,s)::t)` by METIS_TAC [rtc2list_distrib_append_fst,
						    APPEND,MEM,MEM_APPEND,
						    APPEND_ASSOC] THEN
       `(LAST ((q,i,s)::t) = (q'',q''',r'))` by METIS_TAC [last_elem,APPEND] THEN
       `(FRONT ((q,i,s)::(t ++ [x]))) = ((q,i,s)::t)`
       by METIS_TAC [APPEND,APPEND_ASSOC,frontAppendFst] THEN
       `(∀qx ix sx.
               MEM (qx,ix,sx) (FRONT ((q,i,s)::t)) ⇒
               LENGTH s ≤ LENGTH sx)` by METIS_TAC [APPEND_FRONT_LAST,MEM,
						    MEM_APPEND] THEN
       `(s = []) ∨ ∃p. r' = p ++ TL s` by METIS_TAC [] THEN
       SRW_TAC [][] THEN
       Cases_on `p'=[]` THEN1
       (SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN
	`LENGTH s ≤ LENGTH (TL s)` by METIS_TAC [APPEND,MEM,MEM_APPEND,APPEND_ASSOC,
						 frontAppendFst] THEN
	Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	FULL_SIMP_TAC (arith_ss) []) THEN
       Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       `((q,i,s)::(t ++ [x])) = [(q,i,s)]++(t++[x])` by SRW_TAC [][] THEN
       `x=(q',i',s')` by METIS_TAC [last_elem,APPEND] THEN
       `rtc2list (ID p) ([(q'',q''',h::(t' ++ TL s))]++[(q',i',s')])`
       by METIS_TAC [rtc2list_distrib_append_snd,MEM,MEM_APPEND,APPEND_ASSOC] THEN
       FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
       SRW_TAC [][]]);

val frontLem1 = store_thm
("frontLem1",
``∀q inp stk q0 i0 s0 spfx.
   (ID p) ⊢ dl ◁ (q,inp,stk) → (q0,i0,s0) ∧
   (∀q' i' s'.MEM (q',i',s') dl ⇒ (LENGTH stk <= LENGTH s'))
      ⇒
      ∃stk0 stk1 s0'.(stk=stk0++stk1) ∧ (s0=s0'++stk1)``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND,NOT_CONS_NIL,pdastk] THEN
`t=FRONT t ++[LAST t]`by METIS_TAC [APPEND_FRONT_LAST] THEN
SRW_TAC [][] THEN
 `LENGTH (FRONT t) < LENGTH t` by METIS_TAC [frontLen] THEN
`LENGTH ((q,inp,stk)::FRONT t) < SUC (LENGTH t)` by
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
`rtc2list (ID p) ((q,inp,stk)::FRONT t)`
 by METIS_TAC [APPEND,rtc2list_distrib_append_fst,MEM,MEM_APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((q,inp,stk)::FRONT t)`] MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`((q,inp,stk)::FRONT t)`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `FRONT t =[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      `rtc2list (ID p) ((q,inp,stk0 ++ stk1)::[LAST t])` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `LAST t` THEN
      Cases_on `r` THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      (SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [APPEND]),

      `FRONT t = FRONT (FRONT t) ++ [LAST (FRONT t)]`
      by METIS_TAC [APPEND_FRONT_LAST] THEN
      Cases_on `LAST (FRONT t)` THEN
      Cases_on `r` THEN
      `(LAST ((q,inp,stk)::FRONT t) = (q',q'',r'))` by METIS_TAC [last_append,
								  APPEND] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`q''`,`r'`] MP_TAC) THEN SRW_TAC [][] THEN
      `(∀q' i' s'.
               (q' = q) ∧ (i' = inp) ∧ (s' = stk) ∨
               MEM (q',i',s') (FRONT t) ⇒
               LENGTH stk ≤ LENGTH s')` by METIS_TAC [MEM_APPEND] THEN
      `∃stk0 stk1 s0''.
              (stk = stk0 ++ stk1) ∧ (r' = s0'' ++ stk1)` by METIS_TAC [] THEN
      SRW_TAC [][] THEN
      `LAST t = (q0,i0,s0)` by METIS_TAC [last_append,APPEND] THEN
      `rtc2list (ID p) (((q,inp,stk0 ++ stk1)::FRONT (FRONT t)) ++
			([(q',q'',s0'' ++ stk1)] ++ [LAST t]))`
      by METIS_TAC [APPEND_ASSOC,APPEND] THEN
      `rtc2list (ID p) ([(q',q'',s0'' ++ stk1)]++[(q0,i0,s0)])`
      by METIS_TAC [MEM,MEM_APPEND,rtc2list_distrib_append_snd] THEN
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      (`s0''++stk1 = [sh]++st`  by METIS_TAC [APPEND] THEN
       IMP_RES_TAC twoListAppEq THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [APPEND])]);


val frontLem1' = store_thm
("frontLem1'",
``∀q inp stk q0 i0 s0 spfx.
   (ID p) ⊢ dl ◁ (q,inp,stk) → (q0,i0,s0) ∧ (stk ≠ []) ∧
   (∀q' i' s'.MEM (q',i',s') dl ⇒ (LENGTH stk <= LENGTH s'))
      ⇒
      ∃stk1 s0'.(stk=HD stk::stk1) ∧ (s0=s0'++stk1)``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [APPEND]) THEN
`t=FRONT t ++[LAST t]`by METIS_TAC [APPEND_FRONT_LAST] THEN
SRW_TAC [][] THEN
 `LENGTH (FRONT t) < LENGTH t` by METIS_TAC [frontLen] THEN
`LENGTH ((q,inp,stk)::FRONT t) < SUC (LENGTH t)` by
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
`rtc2list (ID p) ((q,inp,stk)::FRONT t)`
 by METIS_TAC [APPEND,rtc2list_distrib_append_fst,MEM,MEM_APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((q,inp,stk)::FRONT t)`] MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`((q,inp,stk)::FRONT t)`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `FRONT t =[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      `rtc2list (ID p) ((q,inp,s0'' ++ stk1)::[LAST t])` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `LAST t` THEN
      Cases_on `r` THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      (SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [APPEND]),

      `FRONT t = FRONT (FRONT t) ++ [LAST (FRONT t)]`
      by METIS_TAC [APPEND_FRONT_LAST] THEN
      Cases_on `LAST (FRONT t)` THEN
      Cases_on `r` THEN
      `(LAST ((q,inp,stk)::FRONT t) = (q',q'',r'))` by METIS_TAC [last_append,
								  APPEND] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`q''`,`r'`] MP_TAC) THEN SRW_TAC [][] THEN
      `(∀q' i' s'.
               (q' = q) ∧ (i' = inp) ∧ (s' = stk) ∨
               MEM (q',i',s') (FRONT t) ⇒
               LENGTH stk ≤ LENGTH s')` by METIS_TAC [MEM_APPEND] THEN
      `∃stk1 s0'.
              (stk = HD stk::stk1) ∧ (r' = s0' ++ stk1)` by METIS_TAC [] THEN
      SRW_TAC [][] THEN
      `LAST t = (q0,i0,s0)` by METIS_TAC [last_append,APPEND] THEN
      `rtc2list (ID p) (((q,inp,HD stk::stk1)::FRONT (FRONT t)) ++
			([(q',q'',s0' ++ stk1)] ++ [LAST t]))`
      by METIS_TAC [APPEND_ASSOC,APPEND] THEN
      `rtc2list (ID p) ([(q',q'',s0' ++ stk1)]++[(q0,i0,s0)])`
      by METIS_TAC [MEM,MEM_APPEND,rtc2list_distrib_append_snd] THEN
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      (`s0'++stk1 = [sh]++st` by METIS_TAC [APPEND] THEN
       IMP_RES_TAC twoListAppEq THEN
       SRW_TAC [][] THEN1
       METIS_TAC [APPEND] THEN1 METIS_TAC [APPEND] THEN
       `LENGTH (HD stk::(s1++s2)) ≤ LENGTH (sh::s2)`
       by METIS_TAC [MEM,MEM_APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `LENGTH s1 = 0` by DECIDE_TAC THEN
       METIS_TAC [LENGTH_NIL,APPEND])]);



val lem1 = store_thm
("lem1",
``∀q inp stk q0 i0 s0 spfx.
   (ID p) ⊢ dl ◁ (q,inp,stk) → (q0,i0,s0) ∧
   (LENGTH s0 = LENGTH stk - 1) ⇒ (stk≠[]) ⇒
   (∀q' i' s'.MEM (q',i',s') (FRONT dl) ⇒ (LENGTH stk <= LENGTH s'))
      ⇒
      (stk=HD stk::s0)``,

 SRW_TAC [][] THEN
 Cases_on `dl=[]` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 `dl=FRONT dl++[LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
 Cases_on `FRONT dl=[]` THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `s0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DECIDE_TAC) THEN
 `ID p ⊢ FRONT dl ◁ (q,inp,stk) →  LAST (FRONT dl)`
 by METIS_TAC [listderivfront] THEN
 Cases_on `LAST (FRONT dl)` THEN
 Cases_on `r` THEN
`∃stk1 s0'.(stk = HD stk::stk1) ∧ (r' = s0' ++ stk1)`
 by METIS_TAC [frontLem1'] THEN
 `ID p (q',q'',r') (q0,i0,s0)` by
(Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 `rtc2list (ID p) (FRONT (FRONT ((q,inp,stk)::t)) ++
		   [(q',q'',s0' ++ stk1)] ++ [(q0,i0,s0)])`
 by METIS_TAC [APPEND,APPEND_FRONT_LAST,NOT_CONS_NIL] THEN
 `rtc2list (ID p) ([(q',q'',s0' ++ stk1)] ++ [(q0,i0,s0)])`
 by METIS_TAC [rtc2list_distrib_append_snd,MEM,MEM_APPEND,APPEND_ASSOC] THEN
 FULL_SIMP_TAC (srw_ss()) []) THEN
 FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
 (`[sh]++st = s0'++stk1` by METIS_TAC [APPEND] THEN
      IMP_RES_TAC twoListAppEq THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[

      `LENGTH st' + LENGTH st = LENGTH (HD stk::st) − 1` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [LENGTH_NIL,APPEND_NIL],

      Cases_on `s0'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
      `LENGTH st' + LENGTH s2' = LENGTH (HD stk::([sh] ++ s2')) − 1`
      by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH stk = LENGTH (HD stk::sh::s2')` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      `SUC (SUC (LENGTH s2')) ≤ LENGTH (sh::s2')`
      by METIS_TAC [MEM,MEM_APPEND,APPEND_FRONT_LAST] THEN
      FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],

      `LENGTH st' + LENGTH s2' = LENGTH (HD stk::s2') − 1` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [APPEND_NIL,LENGTH_NIL]
      ],

      `LENGTH st' + (LENGTH s1 + LENGTH s2) =
          LENGTH (HD stk::s2) − 1` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `(LENGTH s1 = 0) ∧ (LENGTH st'=0)` by DECIDE_TAC THEN
      METIS_TAC [LENGTH_NIL,APPEND_NIL]
      ]));


val ldIdcSplit = store_thm
("ldIdcSplit",
``∀dl q inp stk qf.
 (ID p) ⊢ dl ◁ (q,inp,stk) → (qf,[],[])
    ⇒
   ∃dl0 q0 i0 s0 spfx.
   (ID p) ⊢ dl0 ◁ (q,inp,stk) → (q0,i0,s0) ∧
   (LENGTH s0 = LENGTH stk - 1) ∧
   (∀q' i' s'.MEM (q',i',s') (FRONT dl0) ⇒ (LENGTH stk <= LENGTH s')) ∧
   ((∃dl1.(ID p) ⊢ dl1 ◁ (q0,i0,s0) → (qf,[],[]) ∧
     (LENGTH dl1 < LENGTH dl) ∧ (LENGTH dl0 < LENGTH dl)) ∨
    ((q0,i0,s0) = (qf,[],[])))``,

SRW_TAC [][] THEN
`stkLen (LAST dl) = 0` by METIS_TAC [pdastk, LENGTH, stkLen, listderiv_def] THEN
`(∀i.i + 1 < LENGTH dl ∧ stkLen (EL (i + 1) dl) < stkLen (EL i dl) ⇒
   (stkLen (EL i dl) = stkLen (EL (i + 1) dl) + 1))` by METIS_TAC [ldIdcStkLen] THEN
`dl ≠ []` by (SPOSE_NOT_THEN ASSUME_TAC THEN
	      FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
`∀n.n ≤ stkLen (HD dl) ⇒
   ∃i.(stkLen (EL i dl) = n) ∧ i < LENGTH dl ∧
   ∀j. j < i ⇒ n < stkLen (EL j dl)` by METIS_TAC [stackRedGen] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`stkLen (HD dl) -1`] MP_TAC) THEN
 SRW_TAC [][] THEN
`∃l1 l2. (dl = l1 ++ [EL i dl] ++ l2) ∧ (LENGTH l1 = i)`
by METIS_TAC [elMemLen] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `EL (LENGTH l1) dl` THEN Cases_on `r` THEN
MAP_EVERY Q.EXISTS_TAC [`l1++[(q',q'',r')]`,`q'`,`q''`,`r'`] THEN
SRW_TAC [][]
THENL[
      METIS_TAC [rtc2list_distrib_append_fst, APPEND_ASSOC,MEM,MEM_APPEND],

      Cases_on `l1` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],

      METIS_TAC [last_elem],

      FULL_SIMP_TAC (srw_ss()) [stkLen,pdastk],

      FULL_SIMP_TAC (srw_ss()) [frontAppendFst] THEN
      FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
      RES_TAC THEN
      Cases_on `l1` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `n < LENGTH (h::t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
      `EL n (h::(t ++ [(q',q'',r')] ++ l2)) = EL n (h::t) `
      by METIS_TAC [EL_APPEND1, APPEND, APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [stkLen, pdastk] THEN
      METIS_TAC [pdastk, DECIDE ``a<1+b ⇔ a≤b``],

      Cases_on `l2=[]` THEN1
      (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      `(q',q'',r') = (qf,[],[])` by METIS_TAC [last_elem] THEN
      FULL_SIMP_TAC (srw_ss()) []) THEN
      DISJ1_TAC THEN
      Q.EXISTS_TAC `(q',q'',r')::l2` THEN SRW_TAC [][]
      THENL[
	    METIS_TAC [rtc2list_distrib_append_snd,APPEND,MEM,MEM_APPEND,
		       APPEND_ASSOC],

	    METIS_TAC [last_append, NOT_CONS_NIL, APPEND],


	    Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN1
	    (FULL_SIMP_TAC (srw_ss()) [stkLen,pdastk] THEN
	     `r'≠[]`  by (SPOSE_NOT_THEN ASSUME_TAC THEN
			  Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  Cases_on `h` THEN Cases_on `r` THEN
			  FULL_SIMP_TAC (srw_ss()) [id_thm]) THEN
	     `LENGTH r' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
	     DECIDE_TAC) THEN
	    DECIDE_TAC,

	    Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
	    ]]);

val idcStkNil = store_thm
("idcStkNil",
``∀x y.(ID p)^* x y ⇒ (x=(q,i,[])) ⇒ (y=(q',i',[])) ⇒ (x=y)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Cases_on `x'` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][]);

val rtc2listLastMemState = store_thm
("rtc2listLastMemState",
``∀q i s t.rtc2list (ID p) ((q,i,s)::t) ∧ (t≠[]) ⇒
   MEM (pdastate (LAST t)) (statesList p p.next)``,

SRW_TAC [][] THEN
`t=FRONT t ++ [LAST t]` by METIS_TAC [APPEND_FRONT_LAST]  THEN
Cases_on `FRONT t=[]` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      `rtc2list (ID p) ((q,i,s)::[LAST t])` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `LAST t` THEN Cases_on `r` THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [pdastate] THEN
      METIS_TAC [memStateRule],


      `rtc2list (ID p) ([(q,i,s)]++ FRONT (FRONT t) ++ [LAST (FRONT t)] ++ [LAST t])`
			  by METIS_TAC [APPEND_FRONT_LAST,APPEND_ASSOC,APPEND] THEN
      `rtc2list (ID p) ([LAST (FRONT t)] ++ [LAST t])`
      by METIS_TAC [MEM,MEM_APPEND, rtc2list_distrib_append_snd,APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `LAST (FRONT t)` THEN Cases_on `r` THEN
      Cases_on `LAST t` THEN Cases_on `r` THEN
      FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [pdastate] THEN
      METIS_TAC [memStateRule]
      ]);


val rtc2listFstMemState = store_thm
("rtc2listFstMemState",
``∀q i s t.rtc2list (ID p) ((q,i,s)::t) ∧ (t≠[]) ⇒
   MEM q (statesList p p.next)``,

SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `h` THEN Cases_on `r` THEN
 FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [pdastate] THEN
 METIS_TAC [memStateRule]);


val _ = export_theory ();
