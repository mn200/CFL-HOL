open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory

open listLemmasTheory containerLemmasTheory relationLemmasTheory
    pdaDefTheory


val _ = new_theory "laeslafs"


val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1
val _ = diminish_srw_ss ["list EQ"];



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
FULL_SIMP_TAC (srw_ss()) [ID_def]);


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
SRW_TAC [][ID_def] THEN
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
   Cases_on `inp` THEN SRW_TAC [][ID_def] THEN
   METIS_TAC [newmQeRule, MEM, ID_def, APPEND],

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
SRW_TAC [][newm, LET_THM, ID_def] THEN
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
   FULL_SIMP_TAC (srw_ss()) [stkSymsList_def, rgr_r9eq, ssymslApp,
                          stkSymsList'_def] THEN
   METIS_TAC [APPEND, APPEND_ASSOC]);


val idMemStkSyms = store_thm
("idMemStkSyms",
``m ⊢ (q,s0,stk) → (q',s1,stk') ∧
  (∀e. MEM e stk ⇒ MEM e (stkSymsList m m.next))
       ⇒
    ∀e. MEM e stk' ⇒ MEM e (stkSymsList m m.next)``,

  Cases_on `s0` THEN Cases_on `stk` THEN
  SRW_TAC [][ID_def] THEN
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

  SRW_TAC [][stkSymsList_def, newm, LET_THM] THEN
  SRW_TAC [][stkSymsList'_def]);



val stkSymsFst = store_thm
("stkSymsFst",
``∀sl stl.∀e.MEM e (stkSymsList' (finalStateTrans q stl sl))
      ⇒
    MEM e sl``,
Induct_on `sl` THEN Induct_on `stl` THEN
SRW_TAC [][finalStateTrans, stkSymsList'_def]
THENL[
METIS_TAC [MEM, MEM_APPEND, APPEND],

FULL_SIMP_TAC (srw_ss()) [fst1, stkSymsList'_def, ssymslApp,
                          finalStateTrans] THEN
METIS_TAC [MEM, MEM_APPEND, APPEND]
]);


val stkSymsNst = store_thm
("stkSymsNst",
``∀sl.∀e.MEM e (stkSymsList' (newStateTrans q sl))
      ⇒
    MEM e sl``,
Induct_on `sl` THEN
SRW_TAC [][newStateTrans, stkSymsList'_def] THEN
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

SRW_TAC [] [stkSymsList_def]
THENL[
   FULL_SIMP_TAC (srw_ss()) [newm, LET_THM],

   FULL_SIMP_TAC (srw_ss()) [newm, LET_THM, ssymslApp,
                             stkSymsList'_def]
   THENL[
	 FULL_SIMP_TAC (srw_ss()) [stkSymsList_def] THEN
	 METIS_TAC [stkSymsFst, MEM],

	 FULL_SIMP_TAC (srw_ss()) [stkSymsList_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [lafs_def] THEN
SRW_TAC [][newm, LET_THM] THEN
Q.MATCH_ABBREV_TAC `x ∈ laes <| start := q0';
                                ssSym := x0;
				next := d';
				final := [] |>` THEN
Q.MATCH_ABBREV_TAC `x ∈ laes m'` THEN
`IDC m' (q0',x,[x0]) (m.start,x,m.ssSym::[x0])` by
(SRW_TAC [][] THEN
SRW_TAC [] [Once RTC_CASES1] THEN
Q.EXISTS_TAC `(m.start,x,[m.ssSym;x0])` THEN
SRW_TAC [][ID_def] THEN
Cases_on `x` THEN SRW_TAC [][ID_def] THEN
UNABBREV_ALL_TAC THEN
SRW_TAC [][]) THEN
`IDC m' (m.start,x,[m.ssSym]) (state,[],stack)`
   by METIS_TAC [idcLafsImpLaes, newm, LET_THM, APPEND] THEN
`IDC m' (m.start,x,[m.ssSym]++[x0]) (state,[],stack++[x0])`
  by METIS_TAC [idcStackInsert, APPEND, newm, LET_THM] THEN

`(MEM x0 (stkSymsList m' m'.next) ∧
    MEM m.ssSym (stkSymsList m' m'.next))`
    by METIS_TAC [memNewmStkSyms, newm, LET_THM, APPEND] THEN
`∀e. MEM e stack ⇒ MEM e (stkSymsList m' m'.next)`
    by METIS_TAC [idcMemStkSyms, MEM] THEN
`∀e. MEM e stack ⇒ ((e=x0) ∨ MEM e (stkSymsList m m.next))`
       by METIS_TAC [memOldmStkSyms,newm, LET_THM, APPEND] THEN
`(∀e.
          MEM e (stack++[x0]) ⇒
          MEM e (stkSymsList m m.next) ∨ (e = x0))`
  by METIS_TAC  [MEM, MEM_APPEND] THEN
`¬(stack++[x0] = [])` by SRW_TAC [][] THEN
`IDC m' (state,[],stack++[x0]) (qe,[],[])`
      by METIS_TAC [idcNewmPopStk, newm,
                    LET_THM, APPEND] THEN
SRW_TAC [][laes_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `qe` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`m'.start = q0'` by SRW_TAC [][Abbr `m'`] THEN
`m'.ssSym = x0` by SRW_TAC [][Abbr `m'`] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [ RTC_RTC, APPEND]);



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
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
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
      FULL_SIMP_TAC (srw_ss()) [states_def],

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
	     FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
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
	    METIS_TAC [rtc2listRtcHdLast, HD, RTC_RULES, NOT_CONS_NIL]]]);



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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[

FULL_SIMP_TAC (srw_ss()) [stkSyms_def] THEN
METIS_TAC [],

METIS_TAC [toStEqFst],

METIS_TAC [toStEqNst],

FULL_SIMP_TAC (srw_ss()) [stkSyms_def] THEN
METIS_TAC [],

METIS_TAC [notSomeInpMemFst],

METIS_TAC [notSomeInpMemNst],

FULL_SIMP_TAC (srw_ss()) [stkSyms_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
SRW_TAC [][newm, LET_THM, ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
SRW_TAC [][ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [newm, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
   FULL_SIMP_TAC (srw_ss()) [newm, LET_THM, ID_def],

   `((q0',i,[x0])=(q',i',s')) ∨
    ∃u.ID (newm m (q0',x0,qe)) (q0',i,[x0]) u ∧
    (ID (newm m (q0',x0,qe)))^* u (q',i',s')`
       by METIS_TAC [RTC_CASES1] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN
   SRW_TAC [][] THEN
   Cases_on `u` THEN
   Cases_on `r` THEN
   METIS_TAC [idNewmFstStep]]);



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
FULL_SIMP_TAC (srw_ss()) [lafs_def, laes_def] THEN
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
`st' ∈ states m` by FULL_SIMP_TAC (srw_ss()) [states_def] THEN
`m.start ∈ states m` by FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
`m.ssSym ≠ x0` by FULL_SIMP_TAC (srw_ss()) [stkSyms_def] THEN
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


val thm51 = store_thm
("thm51",
``INFINITE univ(:'ssym) ∧ INFINITE univ(:'state)
      ⇒
     ∀m.∃m'. (lafs (m:('isym, 'ssym, 'state) pda) =
             laes (m':('isym, 'ssym, 'state) pda))``,

SRW_TAC [] [EQ_IMP_THM, EXTENSION] THEN
`FINITE (stkSyms m)`
     by METIS_TAC [finiteStkSyms, FINITE_LIST_TO_SET] THEN
`?x0.x0 IN U1 ∧ ~(x0 IN (stkSyms m))`
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_ssym_exists] THEN
`FINITE (states m)`
     by METIS_TAC [finiteStates, FINITE_LIST_TO_SET] THEN
`?q0.q0 IN U2 ∧ ~(q0 IN (states m))`
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists] THEN
`∃qe.qe ∈ U2 ∧ (qe ∉ (q0 INSERT states m))`
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists,
		  FINITE_INSERT] THEN
`(q0 ≠ qe) ∧ (qe ∉ states m)` by FULL_SIMP_TAC (srw_ss()) [] THEN
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
        MAP (toFinalStateTrans x0 qf) (statesList p)
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
FULL_SIMP_TAC (srw_ss()) [ID_def]);


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
  (MEM state (statesList m))
     ⇒
  MEM ((NONE,x0,state),qf,[]) m'.next``,

SRW_TAC [][newm', LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][toFinalStateTrans] THEN
METIS_TAC []);


val memStartStateNewm' = store_thm
("memStartStateNewm'",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m) ∧
  (m'=(newm' m (q0',x0,qf)))
     ⇒
   MEM m.start (statesList m')``,

SRW_TAC [][newm', LET_THM] THEN
SRW_TAC [][statesList_def] THEN
METIS_TAC [rich_listTheory.CONS_APPEND, statesListApp,
           statesList'_def, MEM]);


val toStEqFs = store_thm (
"toStEqFs",
``∀fsl sl'.MEM ((NONE,h',q),q',sl)
                (MAP (toFinalStateTrans x0 qf) stl)
               ⇒
            (q'=qf) ∧ (sl=[]) ∧ (h'=x0)``,

Induct_on `stl` THEN
SRW_TAC [][toFinalStateTrans] THEN
METIS_TAC []);

val toFsTrans = store_thm
("toFsTrans",
``¬(x0 ∈ stkSyms m) ∧
  ¬(q0' ∈ states m) ∧
  ¬(qf ∈ states m) ∧
  state ∈ states m ∧
  (m'=(newm' m (q0',x0,qf)))
        ⇒
   MEM ((NONE,x0,state),qf,[]) m'.next``,

SRW_TAC [][newm', LET_THM] THEN
`MEM state (statesList m)`
    by METIS_TAC [mem_in, states_list_eqresult] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]THEN
SRW_TAC [][statesList_def, statesList'_def, toFinalStateTrans] THEN
METIS_TAC []);



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
(SRW_TAC [][] THEN
SRW_TAC [] [Once RTC_CASES1] THEN
Q.EXISTS_TAC `(m.start,x,[m.ssSym;x0])` THEN
SRW_TAC [][ID_def] THEN
Cases_on `x` THEN SRW_TAC [][ID_def] THEN
UNABBREV_ALL_TAC THEN
SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [laes_def] THEN
`IDC m' (m.start,x,[m.ssSym]) (state,[],[])`
   by METIS_TAC [idcLaesImpLafs', newm', LET_THM, APPEND] THEN
SRW_TAC [][lafs_def] THEN
`IDC m' (m.start,x,m.ssSym::[x0])
        (state,[],[x0])`
          by METIS_TAC [ APPEND, idcStackInsert] THEN
`MEM m.start (statesList m)`
   by FULL_SIMP_TAC (srw_ss()) [statesList_def] THEN
`MEM state (statesList m)`
    by METIS_TAC [memState] THEN
`state ∈ states m` by METIS_TAC [mem_in, states_list_eqresult] THEN
`MEM ((NONE,x0,state),qf,[]) m'.next`
     by METIS_TAC [toFsTrans, Abbr `m'`, newm', LET_THM,
		   APPEND] THEN
`ID m' (state,[],[x0]) (qf,[],[])`
  by SRW_TAC [][ID_def] THEN
MAP_EVERY Q.EXISTS_TAC [`qf`, `[]`]  THEN
SRW_TAC [][] THEN
`IDC m' (state,[],[x0]) (qf,[],[])`
    by SRW_TAC [][RTC_RULES] THEN
`MEM qf m'.final` by SRW_TAC [][Abbr `m'`] THEN
`m'.start = q0'` by SRW_TAC [][Abbr `m'`] THEN
`m'.ssSym = x0` by SRW_TAC [][Abbr `m'`] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [RTC_RTC]);



val notSomeInpMemFst' = store_thm (
"notSomeInpMemFst'",
``∀fsl sl'.¬MEM ((SOME h,h',q),q',sl)
                (MAP (toFinalStateTrans x0 qf) stl)``,

Induct_on `stl` THEN
SRW_TAC [][toFinalStateTrans]);


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
SRW_TAC [][newm', LET_THM, ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
SRW_TAC [][newm', LET_THM, ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [states_def] THEN
      METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN
      METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
SRW_TAC [][ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [newm', LET_THM]
THENL[
      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

      METIS_TAC [notSomeInpMemFst'],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

      METIS_TAC [memFslFst', states_list_eqresult, mem_in],

      FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

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
FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [ID_def]
THENL[

  FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

  FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

  METIS_TAC [memFslFst', mem_in, states_list_eqresult],

  FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

  METIS_TAC [notSomeInpMemFst'],

  FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

  FULL_SIMP_TAC (srw_ss()) [states_def] THEN METIS_TAC [],

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
SRW_TAC [][newm', LET_THM, ID_def] THEN
FULL_SIMP_TAC (srw_ss()) [states_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [lafs_def, laes_def] THEN
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
SRW_TAC [][] THEN1 FULL_SIMP_TAC (srw_ss()) [states_def] THEN
Cases_on `u'` THEN Cases_on `r` THEN
`(q''=[])` by METIS_TAC [newm'toFs] THEN
`q ∈ states m`  by METIS_TAC [toFsFromOldSt] THEN
`m.start ∈ states m` by FULL_SIMP_TAC (srw_ss()) [states_def] THEN
`(ID m)^* (m.start,q',[m.ssSym; x0]) (q,q'',r')`
    by METIS_TAC [idcNewm'ImpOldm] THEN
IMP_RES_TAC idcStkPop THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`[m.ssSym]`] MP_TAC) THEN
SRW_TAC [][] THEN
`x0 ≠ m.ssSym` by FULL_SIMP_TAC (srw_ss()) [stkSyms_def] THEN
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



val thm52 = store_thm
("thm52",
``INFINITE (U1 : 'ssym set) ∧ INFINITE (U2 : 'state set)
     ⇒
   ∀m.∃m'.laes (m:('isym, 'ssym, 'state) pda) =
          lafs (m':('isym, 'ssym, 'state) pda)``,
SRW_TAC [] [EQ_IMP_THM, EXTENSION] THEN
`FINITE (stkSyms m)`
     by METIS_TAC [finiteStkSyms, FINITE_LIST_TO_SET] THEN
`∃x0.x0 IN U1  ∧ x0 ∉ stkSyms m`
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_ssym_exists] THEN
`FINITE (states m)`
     by METIS_TAC [finiteStates, FINITE_LIST_TO_SET] THEN
`∃q0'.q0' IN U2  ∧ q0' ∉ states m`
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists] THEN
`∃qf.qf IN U2  ∧ qf ∉ (q0' INSERT states m)`
    by METIS_TAC [IN_INFINITE_NOT_FINITE, new_state_exists,
		  FINITE_INSERT] THEN
FULL_SIMP_TAC (srw_ss()) [INSERT_DEF] THEN
Q.EXISTS_TAC `newm' m (q0',x0,qf)` THEN
SRW_TAC [][] THEN
METIS_TAC [laesImpLafs', lafsImpLaes']);

val _ = export_theory ();
