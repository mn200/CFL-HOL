open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory

open listLemmasTheory relationLemmasTheory containerLemmasTheory
     grammarDefTheory pdaDefTheory symbolDefTheory parseTreeTheory

val _ = new_theory "homomorphism"

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val stkSymsInPda = Define
`stkSymsInPda m ssyms = ∀e.MEM e ssyms ⇒ e ∈ stkSyms m`;


val memStkSyms = store_thm
("memStkSyms",
``∀ssyms'.
MEM ((io,ssym,q),q',ssyms') m.next
⇒
ssym ∈ stkSyms m ∧ (∀e.MEM e ssyms' ⇒ e ∈ stkSyms m)``,

SRW_TAC [][stkSyms_def, EXTENSION] THEN1
METIS_TAC [] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [mem_in]);



val stkSymsPdaInv = store_thm
("stkSymsPdaInv",
``∀x y.(ID m)^* x y ⇒ 
∀q i s.(x=(q,i,s)) ⇒ (y=(q',i',s')) ⇒ stkSymsInPda m s
⇒
stkSymsInPda m s'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Cases_on `x'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [stkSymsInPda] THEN
SRW_TAC [][] THEN
`sh ∈ stkSyms m` by (FULL_SIMP_TAC (srw_ss()) [stkSyms_def, EXTENSION] THEN
 METIS_TAC []) THEN
 `∀e.MEM e st' ⇒  e ∈ stkSyms m` 
 by METIS_TAC [memStkSyms] THEN
METIS_TAC []);

val memld = store_thm
("memld",
``R ⊢ dl ◁ x ↝ y ⇒ MEM x dl ∧ MEM y dl``,

Cases_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [last_append, APPEND, APPEND_FRONT_LAST, MEM_APPEND,MEM]);


val ldImprtc2list = store_thm
("ldImprtc2list",
``∀dl x y.R ⊢ dl ◁ x → y ⇒ R^* x y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
RES_TAC THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC [RTC_RULES]);


val idcStkNil' = store_thm
("idcStkNil'",
``∀x y.(ID m)^* x y ⇒ (x=(q,i,[])) ⇒ (y=(q,i,[]))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Cases_on `x'` THEN 
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm]);

val idcMemStates = store_thm
("idcMemStates",
``∀x y.(ID m)^* x y ⇒ ∀q i s.(x=(q,i,s)) ⇒ (y=(q',i',s')) ⇒ q ∈ states m
⇒
q' ∈ states m``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Cases_on `x'` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
`q'' ∈ states m` by (SRW_TAC [][states_def, EXTENSION] THEN METIS_TAC []) THEN
METIS_TAC []);


val listDiv2 = store_thm
("listDiv2",
``∀l.∃x y.l=x++y``,
Induct_on `l` THEN SRW_TAC [][] THEN
METIS_TAC [APPEND]);

val listDerivLastBrk = store_thm
("listDerivLastBrk",
``R ⊢ l ++ [e] ◁  x → z ∧ (l ≠ [])
 ⇒
R ⊢ l ◁ x → LAST l ∧ (e = z) ∧ R (LAST l) e``,

SRW_TAC [][listderiv_def] THEN1
METIS_TAC [rtc2list_distrib_append_fst] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
`l=FRONT l ++ [LAST l]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`rtc2list R ([LAST l]++[e])` 
 by METIS_TAC [MEM, MEM_APPEND, rtc2list_distrib_append_snd, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) []);


val rule1 = Define
`rule1 m m' h = 
{ ((NONE,ssym,q,x),(p,x),ssyms) | ∃a. isSuffix x (h a) ∧ 
 MEM ((NONE,ssym,q),(p,ssyms)) m.next }`;

val rule2 = Define
`rule2 m m' h =
{ ((NONE,ssym,(q,isym::x)),((p,x),ssyms)) | ∃a. isSuffix (isym::x) (h a) ∧ 
MEM ((SOME isym,ssym,q),(p,ssyms)) m.next }`;

val rule3 = Define
`rule3 (m:(α, β, γ) pda) (m':(α, β, γ # α list) pda) (h: α -> α list) =
{ ((SOME a,ssym,(q,[])),((q,h a),[ssym])) | a,ssym,q |
q ∈ states m ∧ ssym ∈ (stkSyms m ∪ {m'.ssSym}) ∧ (h a) ∈ IMAGE h {a} }`;


val hInvpda = Define
`hInvpda (m:(α, β, γ) pda) (m':(α, β, γ # α list) pda) (h: α -> α list) = 
∃z0. z0 ∉ stkSyms m ∧ (m'.ssSym = z0) ∧ 
∃q0. q0 ∉ states m ∧ (m'.start = (q0,[]:α list)) ∧ 
(∀q r.MEM (q,r:α list) m'.final = MEM q m.final ∧ (r=[])) ∧
∀r.MEM r m'.next = r ∈ (rule1 m m' h ∪ rule2 m m' h ∪ rule3 m m' h) ∪
{ ((NONE,m'.ssSym,m'.start),((m.start,[]),[m.ssSym;m'.ssSym])) } `;


val memMRule1 = store_thm
("memMRule1",
``MEM ((NONE,sh,q),p,st') m.next ∧ hInvpda m m' h ∧ isSuffix x (h a)
⇒
MEM ((NONE,sh,q,x),(p,x),st') m'.next``,

SRW_TAC [][hInvpda] THEN
FULL_SIMP_TAC (srw_ss()) [rule1, rule2] THEN
METIS_TAC []);


val mImpm'Trans1 = store_thm
("mImpm'Trans1",
``MEM ((NONE,sh,q),p,st') m.next ∧ hInvpda m m' h
      ⇒
      IDC m' ((q,[]),[a],sh::st) ((p,h a),[],st' ++ st)``,

 SRW_TAC [][] THEN
`MEM ((NONE,sh,q,h a),(p,h a),st') m'.next`
 by METIS_TAC [memMRule1, isSuffix_refl] THEN
 SRW_TAC [][Once RTC_CASES1] THEN
 `q ∈ states m` by 
 (SRW_TAC [][states_def, EXTENSION] THEN
  METIS_TAC []) THEN
 `sh ∈ stkSyms m'` by (SRW_TAC [][stkSyms_def, EXTENSION] THEN METIS_TAC []) THEN
 `MEM ((SOME a,sh,q,[]),(q,h a),[sh]) m'.next` 
 by (FULL_SIMP_TAC (srw_ss()) [rule3, hInvpda] THEN
     FULL_SIMP_TAC (srw_ss()) [rule2,rule3]  THEN
     RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
     METIS_TAC [memStkSyms]) THEN
 Q.EXISTS_TAC `((q,h a),[],sh::st)` THEN
 SRW_TAC [][id_thm] THEN
 METIS_TAC [APPEND]);

val mImpm'Trans2 = store_thm
("mImpm'Trans2",
``MEM ((SOME ih,sh,q),p,st') m.next ∧ (h a = ih::isyms) ∧ hInvpda m m' h 
 ⇒
IDC m' ((q,[]),[a],sh::st) ((p,isyms),[],st' ++ st)``,

 SRW_TAC [][] THEN
 `isSuffix isyms (h a)` by METIS_TAC [isSuffix_lemma, APPEND] THEN
 `MEM ((NONE,sh,q,ih::isyms),(p,isyms),st')  m'.next`
 by (FULL_SIMP_TAC (srw_ss()) [hInvpda, rule2] THEN
     METIS_TAC [isSuffix_lemma,APPEND]) THEN
 `q ∈ states m` by (SRW_TAC [][states_def, EXTENSION] THEN METIS_TAC []) THEN
 `sh ∈ stkSyms m'` by (SRW_TAC [][stkSyms_def, EXTENSION] THEN METIS_TAC []) THEN
 `MEM ((SOME a,sh,q,[]),(q,h a),[sh]) m'.next` 
 by (FULL_SIMP_TAC (srw_ss()) [hInvpda, rule3] THEN 
     FULL_SIMP_TAC (srw_ss()) [rule1,rule3]  THEN
     RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
     METIS_TAC [memStkSyms]) THEN
 `ID m' ((q,[]),[a],sh::st) ((q,ih::isyms),[],sh::st)`
 by (SRW_TAC [][id_thm] THEN
     METIS_TAC [APPEND]) THEN
 `ID m' ((q, ih::isyms),[],sh::st) ((p,isyms),[],st'++st)`
 by SRW_TAC [][id_thm] THEN
 METIS_TAC [ RTC_RULES]);

val mImpm'OneSym = store_thm
("mImpm'OneSym",
``∀dl p isyms ssyms'.ID m ⊢ dl ◁ (q,h a,ssyms) → (p,isyms,ssyms') ∧ 
LENGTH dl > 1 ∧
hInvpda (m:(α, β, γ) pda) (m':(α, β, γ # α list) pda) (h: α -> α list) 
⇒
 IDC m' ((q,[]),[a],ssyms) ((p,isyms),[],ssyms')``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [][SNOC_APPEND] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH dl = 1) ∨ (LENGTH dl > 1)` by DECIDE_TAC THEN1
(Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
 Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
 SRW_TAC [][] THEN
 METIS_TAC [mImpm'Trans1, mImpm'Trans2]) THEN

`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`ID m ⊢ dl ◁ (q,h a,ssyms) → LAST dl` by METIS_TAC [listDerivLastBrk] THEN
`ID m (LAST dl) x` by METIS_TAC [listDerivLastBrk] THEN
`x = (p,isyms,ssyms')` by METIS_TAC [listDerivLastBrk] THEN
Cases_on `LAST dl` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
RES_TAC
THENL[
      `isSuffix isyms (h a)` by METIS_TAC [APPEND, isSuffix_APPEND, 
					   idcInpSplit] THEN
      IMP_RES_TAC memMRule1 THEN
      `MEM ((NONE,sh,q',isyms),(p,isyms),st') m'.next`
      by (FULL_SIMP_TAC (srw_ss()) [rule2, hInvpda] THEN 
	  METIS_TAC [APPEND, isSuffix_lemma]) THEN
      `ID m' ((q',isyms),[],sh::st) ((p,isyms),[],st' ++ st)`
      by SRW_TAC [][id_thm] THEN
      METIS_TAC [ RTC_RULES_RIGHT1],

      `isSuffix (ih::isyms) (h a)` by METIS_TAC [APPEND, isSuffix_APPEND,
						 idcInpSplit] THEN
      `isSuffix isyms (h a)` by 
      METIS_TAC [isSuffix_APPEND, APPEND, APPEND_ASSOC] THEN
      `MEM ((NONE,sh,q',ih::isyms),(p,isyms),st') m'.next`
      by (FULL_SIMP_TAC (srw_ss()) [rule2, hInvpda] THEN 
	  METIS_TAC [isSuffix_lemma, APPEND]) THEN
      `ID m' ((q',ih::isyms),[],sh::st) ((p,isyms),[],st' ++ st)`
      by SRW_TAC [][id_thm] THEN
      METIS_TAC [ RTC_RULES_RIGHT1]]);


val mImpm'InpNil = store_thm
("mImpm'InpNil",
``∀dl q ssyms p.
ID m ⊢ dl ◁ (q,[],ssyms) → (p,[],ssyms') ∧ hInvpda m m' h 
 ⇒
IDC m' ((q,[]),[],ssyms) ((p,[]),[],ssyms')``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `h'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
`∀a.isSuffix [] (h a)` by SRW_TAC [][isSuffix_def] THEN
IMP_RES_TAC memMRule1 THEN
`ID m' ((q,[]),[],sh::st) ((q',[]),[],st' ++ st)`
by SRW_TAC [][id_thm] THEN
METIS_TAC [RTC_RULES]);


val idTransOnInpPfx = store_thm
("idTransOnInpPfx",
``∀q x y ssyms.
      ID m ⊢ dl ◁ (q,x++y,ssyms) → (p,[],ssyms') 
      ⇒
      ∃q0 ssyms0.
      IDC m (q,x++y,ssyms) (q0,y,ssyms0) ∧ IDC m (q0,y,ssyms0) (p,[],ssyms')``,

Induct_on `dl` THEN SRW_TAC [][] THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND_NIL,  RTC_RULES] THEN
Cases_on `h'` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] 
THENL[
      FIRST_X_ASSUM (Q.SPECL_THEN [`x`,`y`] MP_TAC) THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `ID m (q,x++y,sh::st) (q',x++y,st'++st)` by SRW_TAC [][id_thm] THEN
      METIS_TAC [RTC_RULES, RTC_RTC],

      Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
 	    `∃x y.q''=x++y` by METIS_TAC [listDiv2] THEN
	    SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`x`,`y`] MP_TAC) THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Q.EXISTS_TAC `q` THEN
	    Q.EXISTS_TAC `sh::st` THEN
	    SRW_TAC [][] THEN
	    `ID m (q,ih::(x++y),sh::st) (q',(x++y),st'++st)` 
	    by SRW_TAC [][id_thm] THEN
	    METIS_TAC [RTC_RULES, RTC_RTC],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`t'`,`y`] MP_TAC) THEN SRW_TAC [][] THEN
	    `ID m (q,h::(t' ++ y),sh::st) (q',t' ++ y,st' ++ st)` 
	    by SRW_TAC [][id_thm] THEN
	    METIS_TAC [RTC_RULES]
	    ]]);

val idTransOnInpPfxToNil = store_thm
("idTransOnInpPfxToNil",
``∀dl q x y ssyms.
      ID m ⊢ dl ◁ (q,x++y,ssyms) → (p,y,ssyms')
      ⇒
      IDC m (q,x,ssyms) (p,[],ssyms')``,

Induct_on `dl` THEN SRW_TAC [][] THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
      (SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       SRW_TAC [][] THEN
       METIS_TAC [ RTC_RULES, APPEND_NIL, APPEND_11]) THEN

IMP_RES_TAC listDerivHdBrk THEN
`h = (q,x++y,ssyms)` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `h'` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][]
THENL[
      FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`x`,`y`,`st'++st`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `ID m (q,x,sh::st) (q',x,st' ++ st)` by SRW_TAC [][id_thm] THEN
      METIS_TAC [ RTC_RULES],

      SRW_TAC [][] THEN
      Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
      THENL[
	    IMP_RES_TAC ldIdcInpSuffix THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isSuffix_def, IS_PREFIX_APPEND] THEN
	    `LENGTH (REVERSE q'') = LENGTH (REVERSE q'' ++ [ih] ++ l)`
	    by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`t'`,`y`,`st'++st`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m (q,h::t',sh::st) (q',t',st' ++ st)` by SRW_TAC [][id_thm] THEN
	    METIS_TAC [ RTC_RULES]
	    ]]);

val memStkSyms = store_thm
("memStkSyms",
``∀ssyms'.
MEM ((io,ssym,q),q',ssyms') m.next
⇒
ssym ∈ stkSyms m ∧ (∀e.MEM e ssyms' ⇒ e ∈ stkSyms m)``,

SRW_TAC [][stkSyms_def, EXTENSION] THEN1
METIS_TAC [] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [mem_in]);


val m'toBufInpNil = store_thm
("m'toBufInpNil",
``∀dl q ssyms.
ID m' ⊢ dl ◁ ((q,[]),[],ssyms) → ((p,r),[],ssyms') ⇒ hInvpda m m' h 
⇒
(r=[])``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN1 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN 
`h'=((q,[]),[],ssyms)`by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `h''` THEN
Cases_on `q'` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2, rule3,EXTENSION] THEN
SRW_TAC [][] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
(FIRST_X_ASSUM (Q.SPECL_THEN [`p'`,`ssyms++st`]MP_TAC) THEN SRW_TAC [][]) THEN
METIS_TAC []);


val m'toBufNil = store_thm
("m'toBufNil",
``∀dl q e ssyms.
ID m' ⊢ dl ◁ ((q,[]),[e],ssyms) → ((p,r),[],ssyms') ∧ hInvpda m m' h  ∧
(h e = [])
⇒
(r=[])``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN1 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN 
`h'=((q,[]),[e],ssyms)`by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `h''` THEN
Cases_on `q'` THEN
Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2, rule3,EXTENSION] THEN
SRW_TAC [][] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
(FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2, rule3,EXTENSION] THEN
 SRW_TAC [][] THEN
 RES_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
 `hInvpda m m' h ` by FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2, rule3, 
						  EXTENSION] THEN
 METIS_TAC [m'toBufInpNil]) THEN
`hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2, rule3, 
						 EXTENSION] THEN
METIS_TAC [m'toBufInpNil]);



val m'Rule1 = store_thm
("m'Rule1",
``MEM ((NONE,sh,q,[]),(q'',r),st') m'.next ∧ hInvpda m m' h 
⇒
(r=[])``,

SRW_TAC [][hInvpda] THEN
`∀a.isSuffix [] (h a)` by SRW_TAC [][isSuffix_def] THEN
FULL_SIMP_TAC (srw_ss()) [rule1, rule2, rule3] THEN
Q.PAT_ASSUM `∀e.P` MP_TAC THEN 
Q.PAT_ASSUM `∀e.P` MP_TAC THEN 
FIRST_X_ASSUM (Q.SPECL_THEN [`((NONE,sh,q,[]),(q'',r),st')`] MP_TAC) THEN 
SRW_TAC [][] THEN
METIS_TAC []);


val idcStkLastStep = store_thm
("idcStkLastStep" ,
``∀x y.(ID m)^* x y ⇒ ∀q i s.
(x=(q,i,s)) ⇒ (y= (q',i',[])) ⇒ (LENGTH s > 0) ⇒
∃q0 i0 e.(ID m)^* (q,i,s) (q0,i0,[e]) ∧ ID m (q0,i0,[e]) (q',i',[])``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Cases_on `x'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][]
THENL[
      Cases_on `st` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    Cases_on `LENGTH st' > 0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  `ID m (q0,i',[e]) (q',i',[])` by SRW_TAC [][id_thm] THEN
		  `ID m (q,i,[sh]) (q'',i,st')` by SRW_TAC [][id_thm] THEN
		  METIS_TAC [RTC_RULES],

		  `ID m (q,i,[sh]) (q'',i,st')` by SRW_TAC [][id_thm] THEN
		  METIS_TAC [RTC_RULES],

		  `LENGTH st' = 0` by DECIDE_TAC THEN
		  `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  MAP_EVERY Q.EXISTS_TAC [`q`,`i`,`sh`] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
		  SRW_TAC [][] THEN
		  Cases_on `u` THEN
		  Cases_on `r` THEN
		  FULL_SIMP_TAC (srw_ss()) [id_thm]
		  ],

	    FULL_SIMP_TAC (arith_ss) [] THEN
	    SRW_TAC [][] THEN
	    (`ID m (q,i,sh::h::t) (q'',i,st' ++ h::t)` 
	     by SRW_TAC [][id_thm] THEN
	     METIS_TAC [RTC_RULES])
	    ],

      Cases_on `st` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    Cases_on `LENGTH st' > 0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][]
	    THENL[
		  `ID m (q,ih::q''',[sh]) (q'',q''',st')` by SRW_TAC [][id_thm] THEN
		  METIS_TAC [RTC_RULES],

		  `ID m (q,ih::q''',[sh]) (q'',q''',st')` by SRW_TAC [][id_thm] THEN
		  METIS_TAC [RTC_RULES],

		  `LENGTH st' = 0` by DECIDE_TAC THEN
		  `st'=[]` by METIS_TAC [LENGTH_NIL] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  MAP_EVERY Q.EXISTS_TAC [`q`,`ih::q'''`,`sh`] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
		  SRW_TAC [][] THEN
		  Cases_on `u` THEN
		  Cases_on `r` THEN
		  FULL_SIMP_TAC (srw_ss()) [id_thm]
		  ],

	    FULL_SIMP_TAC (arith_ss) [] THEN
	    SRW_TAC [][] THEN
	    (`ID m (q,ih::q''',sh::h::t) (q'',q''',st' ++ h::t)` 
	     by SRW_TAC [][id_thm] THEN
	     METIS_TAC [RTC_RULES])
	    ]]);


val memStates = store_thm
("memStates",
``∀dl q i s.ID m ⊢ dl ◁ (q,i,s) → (q',i',s') ∧ LENGTH dl > 1
 ⇒
q ∈ states m ∧ q' ∈ states m``,

Induct_on `dl` THEN SRW_TAC [][] 
THENL[
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      Cases_on `h'` THEN
      Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [states_def, EXTENSION] THEN
      METIS_TAC [],
      
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      Cases_on `h'` THEN
      Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
      SRW_TAC [][] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [states_def, EXTENSION] THEN
      METIS_TAC []]);



val idZ0Inv = store_thm
("idZ0Inv",
``m' ⊢ (q,i,p ++ [m'.ssSym]) → (q0,i0,s0) ∧ hInvpda m m' h 
⇒
∃pfx. s0 = pfx ++ [m'.ssSym]``,

FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2,rule3, EXTENSION] THEN
`p ++ [m'.ssSym] = [sh]++st` by METIS_TAC [APPEND] THEN
IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
(Cases_on `p` THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN 
 SRW_TAC [][] THEN
Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
 METIS_TAC [memStkSyms, APPEND,APPEND_NIL]));

val z0Inv = store_thm
("z0Inv",
``∀dl q i s p.ID m' ⊢ dl ◁ (q,i,s) → (q',i',s') ∧ hInvpda m m' h  ∧
(s=p++[m'.ssSym]) 
⇒
(∀q0 i0 s0.MEM (q0,i0,s0) dl ⇒ ∃pfx.(s0 = pfx++[m'.ssSym]))``,

Induct_on `dl` THEN SRW_TAC [][] 
THENL[
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) []  THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][],
      
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] 
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [idZ0Inv],

	    IMP_RES_TAC listDerivHdBrk THEN
	    `h' = ((q,i,p ++ [m'.ssSym]))` 
	    by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    SRW_TAC [][] THEN
	    Cases_on `h''` THEN
	    Cases_on `r` THEN	    
	    IMP_RES_TAC idZ0Inv THEN
	    SRW_TAC [][] THEN
	    METIS_TAC []]]);


val memStkSymsEq = store_thm
("memStkSymsEq",
``e ∈ stkSyms m = (e=m.ssSym) ∨ 
∃io ssym q q' ssyms.(MEM ((io,ssym,q),q',ssyms) m.next ∧ 
		      ((e=ssym) ∨ MEM e ssyms))``,

SRW_TAC [][stkSyms_def, EXTENSION, EQ_IMP_THM] THEN1
 (Cases_on `out` THEN
  METIS_TAC []) THEN
METIS_TAC [mem_in]);

val memStksymsm' = store_thm
("memStksymsm'",
 ``∀e.e ∈ stkSyms m' ∧ hInvpda m m' h  ⇒ e ∈ stkSyms m ∨ (e=m'.ssSym)``,

SRW_TAC [][memStkSymsEq] THEN
FULL_SIMP_TAC (srw_ss()) [rule1,rule2,rule3,EXTENSION,hInvpda] THEN
SRW_TAC [][] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
METIS_TAC [memStkSyms,memStkSymsEq,MEM,MEM_APPEND]);

val mImpm'HNil = store_thm
("mImpm'HNil",
``∀l1.
hInvpda m m' h  ∧ (∀e.MEM e l1 ⇒ (h e = [])) ∧ (q ∈ states m) ∧
stkSymsInPda m' s
⇒
IDC m' ((q,[]),l1,s++[m'.ssSym]) ((q,[]),[],s++[m'.ssSym])``,

Induct_on `LENGTH l1` THEN SRW_TAC [][] THEN1
METIS_TAC [RTC_RULES,  LENGTH_NIL] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`t`] MP_TAC) THEN SRW_TAC [][] THEN
SRW_TAC [][ Once RTC_CASES1] THEN
 FULL_SIMP_TAC (srw_ss()) [id_thm, hInvpda, rule3, EXTENSION,rule1,rule2] THEN
 Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) [] 
 THENL[
       Q.EXISTS_TAC `((q,[]),t,[m'.ssSym])` THEN
       SRW_TAC [][id_thm] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [ stkSyms_list_eqresult,stkSymsList_def,MEM,MEM_APPEND,
		  mem_in],

       Q.EXISTS_TAC `((q,[]),t,h''::(t'++[m'.ssSym]))` THEN
       SRW_TAC [][id_thm] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `hInvpda m m' h` 
       by FULL_SIMP_TAC (srw_ss()) [rule1,rule2,rule3,EXTENSION,hInvpda] THEN
       METIS_TAC [ stkSymsInPda,stkSymsPdaInv,MEM,memStkSyms,
		  memStksymsm']
       ]);


val idMemStkSyms = store_thm
("idMemStkSyms",
``stkSymsInPda m r' ∧ m ⊢ (q'',q''',r') → (q',i',s')
⇒ stkSymsInPda m s'``,

SRW_TAC [][stkSymsInPda] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
METIS_TAC [memStkSymsEq,MEM,MEM_APPEND]);



val idStkSymsPdaInv = store_thm
("idStkSymsPdaInv",
``m ⊢ (q,i,s) → (q'',q''',r') ∧ stkSymsInPda m s
⇒
stkSymsInPda m r'``,

SRW_TAC [][stkSymsInPda, id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [memStkSymsEq]);

val stkSymsm'Impm = store_thm
("stkSymsm'Impm",
``stkSymsInPda m' l ∧ hInvpda m m' h ⇒ 
(∀e.MEM e l ⇒ e ∈ stkSyms m ∨ (e=m'.ssSym))``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [stkSymsInPda] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1,rule2,rule3,EXTENSION] THEN
 `m.ssSym ∈ stkSyms m` by SRW_TAC [][stkSyms_def] THEN
`e ∈ stkSyms m'` by METIS_TAC [] THEN
IMP_RES_TAC memStkSymsEq THEN
SRW_TAC [][] THEN
Cases_on `io` THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC [memStkSyms]);



val mImpm' = store_thm
("mImpm'",
``∀x dl q ssyms.ID m ⊢ dl ◁ (q,FLAT (MAP h x),ssyms) → (p,[],ssyms') ∧
 hInvpda m m' h  ∧ LENGTH dl > 1 ∧ stkSymsInPda m' ssyms ∧ q ∈ states m
⇒
 IDC m' ((q,[]),x,ssyms++[m'.ssSym]) ((p,[]),[],ssyms'++[m'.ssSym])``,

Induct_on `LENGTH x` THEN SRW_TAC [][] THEN1
 (`x=[]` by METIS_TAC [LENGTH_NIL] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [mImpm'InpNil,idcStackInsert,ldImprtc2list,rtc2list_exists']) THEN
 Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`t`] MP_TAC) THEN SRW_TAC [][] THEN
 IMP_RES_TAC idTransOnInpPfx THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 `∃l.ID m ⊢ l ◁ (q,h h' ++ FLAT (MAP h t),ssyms) → (q0,FLAT (MAP h t),ssyms0)`
 by METIS_TAC [rtc2list_exists'] THEN
 IMP_RES_TAC idTransOnInpPfxToNil THEN
 `∃l'.ID m ⊢ l' ◁ (q,h h',ssyms) → (q0,[],ssyms0)` 
 by METIS_TAC [rtc2list_exists', memld,z0Inv] THEN
 Cases_on `LENGTH l' > 1`
THENL[
      IMP_RES_TAC mImpm'OneSym THEN
      `(ID m')^* ((q,[]),[h'],ssyms) ((q0,[]),[],ssyms0)` 
      by METIS_TAC [rtc2list_exists'] THEN
      `∃dl'.ID m ⊢ dl' ◁ (q0,FLAT (MAP h t),ssyms0) → (p,[],ssyms')`
      by METIS_TAC [rtc2list_exists'] THEN
      Cases_on `LENGTH dl' > 1` THEN1
      (`(ID m')^* ((q,[]),[h'],ssyms++[m'.ssSym]) ((q0,[]),[],ssyms0++[m'.ssSym])` 
       by METIS_TAC [idcStackInsert] THEN
       `q0 ∈ states m` by METIS_TAC [memStates] THEN
       `(ID m')^* ((q0,[]),t,ssyms0 ++ [m'.ssSym])	
       ((p,[]),[],ssyms' ++ [m'.ssSym])` by METIS_TAC [stkSymsPdaInv] THEN
       METIS_TAC [idcInpInsert, RTC_RTC, APPEND,APPEND_NIL]) THEN
      `(LENGTH dl' = 0) ∨ (LENGTH dl' = 1)` by DECIDE_TAC THEN1
      (`dl'=[]` by METIS_TAC [LENGTH_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `t'=[]` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      `(h''= (q0,FLAT (MAP h t),ssyms0)) ∧ (h''= (p,[],ssyms'))`
      by (FULL_SIMP_TAC (srw_ss()) [listderiv_def]  THEN
	  SRW_TAC [][]) THEN
      SRW_TAC [][] THEN
      `FLAT (MAP h t) = []` by SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      `∀e.MEM e t ⇒ (h e = [])` 
      by (SRW_TAC [][] THEN
	  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	  SRW_TAC [][] THEN
	  FULL_SIMP_TAC (srw_ss()) [MEM_FLAT, MAP_APPEND, FLAT_APPEND]) THEN
      `p ∈ states m` by METIS_TAC [memStates] THEN

      `∃l.ID m' ⊢ l ◁ ((q,[]),[h'],ssyms++[m'.ssSym]) → 
      ((p,[]),[],ssyms'++[m'.ssSym])`
      by METIS_TAC [rtc2list_exists',idcStackInsert] THEN
      `LENGTH l'' > 1` by (Cases_on `l''`  THEN
			   FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
			   SRW_TAC [][] THEN
			   Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			   FULL_SIMP_TAC (arith_ss) []) THEN
      `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,
							   rule3,EXTENSION] THEN
      `stkSymsInPda m' ssyms'` by METIS_TAC [stkSymsPdaInv,NOT_CONS_NIL] THEN
      `IDC m' ((p,[]),t,ssyms'++[m'.ssSym]) ((p,[]),[],ssyms'++[m'.ssSym])` 
      by METIS_TAC [mImpm'HNil,MEM,MEM_APPEND] THEN
      METIS_TAC [APPEND,  RTC_RTC, idcInpInsert,ldImprtc2list,
		 idcStackInsert],
      
      `(LENGTH l' = 0) ∨ (LENGTH l' = 1)` by DECIDE_TAC THEN1
      (`l'=[]` by METIS_TAC [LENGTH_NIL] THEN 
       FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
      
      Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `t'=[]` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN
      `(ID m')^* ((q,[]),t,ssyms++[m'.ssSym]) ((p,[]),[],ssyms'++[m'.ssSym])` 
      by METIS_TAC [APPEND_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `h h' = []` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `ssyms` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      IMP_RES_TAC idcStkNil' THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] 
      THENL[
	    Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `h''` THEN Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [id_thm],	    
	    
	    SRW_TAC [][Once RTC_CASES1] THEN
	    Q.EXISTS_TAC `((q,[]),t,h''::(t'++[m'.ssSym]))` THEN
	    FULL_SIMP_TAC (srw_ss()) [rule3, hInvpda, EXTENSION] THEN
	    `q ∈ states m` by METIS_TAC [memStates,listderiv_def] THEN
	    `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) 
	    [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
	    `ID m ⊢ dl ◁
	    (q,FLAT (MAP h t),h''::t') → (p,[],ssyms')`
	    by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN	    
	    `stkSymsInPda m' (h''::(t' ++ [m'.ssSym]))`
	    by (FULL_SIMP_TAC (srw_ss()) [] THEN
		FULL_SIMP_TAC (srw_ss()) [stkSymsInPda] THEN
		SRW_TAC [][] THEN1
		METIS_TAC [] THEN1 	    
		METIS_TAC [] THEN
		SRW_TAC [][stkSyms_def]) THEN
	    `stkSymsInPda m' (ssyms' ++ [m'.ssSym])` by METIS_TAC [stkSymsPdaInv,
						   APPEND,APPEND_ASSOC] THEN
	    `ID m' ((q,[]),h'::t,h''::(t' ++ [m'.ssSym])) 
	    ((q,[]),t,h''::(t' ++ [m'.ssSym]))` by SRW_TAC [][id_thm] THEN
	    FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1, rule2,rule3,EXTENSION] THEN
	    `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) 
	    [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
	    METIS_TAC [stkSymsm'Impm, MEM]
	    ]]);



val stkSymsInPdaApp = store_thm
("stkSymsInPdaApp",
``∀l1 l2.stkSymsInPda m (l1 ++ l2) = stkSymsInPda m l1 ∧ stkSymsInPda m l2``,

Induct_on `l1` THEN SRW_TAC [][stkSymsInPda] THEN
FULL_SIMP_TAC (srw_ss()) [stkSymsInPda] THEN
SRW_TAC [][] THEN
METIS_TAC []);


val idcBufLen = store_thm
("idcBufLen",
``∀x y.(ID m')^* x y ⇒ hInvpda m m' h   ⇒
∀q b i s q' b' s'. (x=((q,b),i,s)) ⇒ (y=((q',b'),i,s'))
⇒
LENGTH b' ≤ LENGTH b``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Cases_on `x'` THEN
Cases_on `q''` THEN
Cases_on `r` THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1,rule2,rule3,EXTENSION] THEN
RES_TAC THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 (`LENGTH (a::q'') ≤ LENGTH q''` 
  by METIS_TAC [ldIdcInpLen,rtc2list_exists'] THEN
  FULL_SIMP_TAC (srw_ss()++ARITH_ss) []));

val rule3Stk = store_thm
("rule3Stk",
``((SOME ih,h',q),q',st') ∈ rule3 m m' h ⇒ (st'=[h'])``,

SRW_TAC [][rule3,EXTENSION]);

val stkSymsPdaInvm'm = store_thm
("stkSymsPdaInvm'm",
``∀x y.(ID m')^* x y ⇒ hInvpda m m' h  ⇒
∀q' i' s'.(x=(q,i,s++[m'.ssSym])) ⇒ (y=(q',i',s'++[m'.ssSym])) ⇒ stkSymsInPda m s
⇒
stkSymsInPda m s'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
Cases_on `y` THEN
Cases_on `r` THEN
`∃pf.r'=pf++[m'.ssSym]` by METIS_TAC [z0Inv,rtc2list_exists',memld] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [stkSymsInPda] THEN
SRW_TAC [][] 
THENL[
      Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss())  [] THEN
	    FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
	    SRW_TAC [][] THEN
	    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN1	    
	    METIS_TAC [MEM,memStkSyms,MEM_APPEND,APPEND_11] THEN1
	    METIS_TAC [MEM,memStkSyms,MEM_APPEND,APPEND_11] THEN1
	    METIS_TAC [MEM,memStkSyms,MEM_APPEND,APPEND_11] THEN
	    `s' = [m.ssSym]` by METIS_TAC [APPEND_11,APPEND] THEN
	    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [stkSyms_def,EXTENSION],

	    `s'=st'++t` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [hInvpda,EXTENSION,rule1]  THEN
	    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
	    THENL[
		  METIS_TAC [memStkSyms],
		  METIS_TAC [memStkSyms],
		  METIS_TAC [memStkSyms],
		  METIS_TAC [memStkSyms],

		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [rule2,EXTENSION] THEN
		  SRW_TAC [][] THEN
		  METIS_TAC [memStkSyms],

		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [rule3,EXTENSION] THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ]],

      Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss())  [] THEN
	    FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
	    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `s'=[]` by METIS_TAC [APPEND_11,APPEND_NIL] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [],
	    
	    
	    SRW_TAC [][] THEN
	    `s'=st'++t` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [hInvpda,EXTENSION,rule1] THEN
	    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
	    FULL_SIMP_TAC (srw_ss()) [rule2,EXTENSION] THEN
	    IMP_RES_TAC rule3Stk THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    ]]);




val m'ImpmNil = store_thm
("m'ImpmNil",
``∀dl q pfx.ID m' ⊢ dl ◁ ((q,[]),[],pfx++[m'.ssSym]) → 
 ((p,[]),[],ssyms'++[m'.ssSym]) ∧ (q ∈ states m) ∧
 hInvpda m m' h ∧ stkSymsInPda m pfx 
 ⇒
IDC m (q,[],pfx) (p,[],ssyms')``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  Cases_on `pfx` THEN SRW_TAC [][] THEN
  METIS_TAC [ RTC_RULES,frontAppendFst]) THEN
IMP_RES_TAC listDerivHdBrk THEN
 `h' = ((q,[]),[],pfx++[m'.ssSym])`by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
 Cases_on `h''` THEN Cases_on `r` THEN
Cases_on `q'` THEN
 FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
      METIS_TAC [memStkSyms] THEN
      `(q0,[]) = (q,[])` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
      
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) 
      [hInvpda,rule1,rule2,rule3,EXTENSION] THENL[
      `stkSymsInPda m ssyms` by METIS_TAC [memStkSyms, stkSymsInPda] THEN
      `stkSymsInPda m ssyms` by METIS_TAC [stkSymsInPda,memStkSyms] THEN
      `stkSymsInPda m (ssyms++t')` by
      METIS_TAC [stkSymsInPdaApp, stkSymsInPda, APPEND] THEN
      `p' ∈ states m` by (SRW_TAC [][states_def, EXTENSION] THEN METIS_TAC []) THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`p'`,`ssyms++t'`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `ID m (q,[],h'::t') (p',[],ssyms++t')` by SRW_TAC [][id_thm] THEN
      METIS_TAC [RTC_RULES],
      `(q0,[]) = (q,[])` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]]]);



val m'StepBufToNil = store_thm
("m'StepBufToNil",
``∀dl q b x pfx.
ID m' ⊢ dl ◁ ((q,b),x,pfx++[m'.ssSym]) → ((p,[]),[],ssyms'++[m'.ssSym]) ∧
hInvpda m m' h 
⇒
∃q0 ssyms0.
IDC m' ((q,b),x,pfx++[m'.ssSym]) ((q0,[]),x,ssyms0++[m'.ssSym]) ∧
IDC m' ((q0,[]),x,ssyms0++[m'.ssSym]) ((p,[]),[],ssyms'++[m'.ssSym])``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [ RTC_RULES, RTC_RTC]) THEN
`h'=((q,b),x,pfx++[m'.ssSym])` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
IMP_RES_TAC listDerivHdBrk THEN
SRW_TAC [][] THEN
Cases_on `h''` THEN
Cases_on `q'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
SRW_TAC [][]
THENL[
      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
      THENL[
	    METIS_TAC [memStkSyms],
	    METIS_TAC [memStkSyms],

	    `(q,b) = (q0,[])` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`m.start`,`[]`,`q'`,`[m.ssSym]`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m'  (m'.start,q',[m'.ssSym]) ((m.start,[]),q',[m.ssSym; m'.ssSym])`
	    by SRW_TAC [][id_thm] THEN
	    Q.EXISTS_TAC `q0'` THEN Q.EXISTS_TAC `ssyms0` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC],

	    
	    FIRST_X_ASSUM (Q.SPECL_THEN [`p'`,`b`,`q'`,`ssyms++t'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' ((q,b),q',h'::(t' ++ [m'.ssSym])) 
	    ((p',b),q',ssyms ++ t' ++ [m'.ssSym])`
	    by (SRW_TAC [][id_thm] THEN METIS_TAC []) THEN
	    Q.EXISTS_TAC `q0''` THEN Q.EXISTS_TAC `ssyms0'`THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC],


	    `ID m' ((q,isym::r'),q',h'::(t' ++ [m'.ssSym])) 
	    ((p',r'),q',ssyms ++ t' ++ [m'.ssSym])`
	    by (SRW_TAC [][id_thm] THEN
		METIS_TAC []) THEN
	    Q.EXISTS_TAC `q0'` THEN Q.EXISTS_TAC `ssyms0`THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC],

	    `(q,b) = (q0,[])` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    `ID m'  (m'.start,q',m'.ssSym::t'++[m'.ssSym]) 
	     ((m.start,[]),q',m.ssSym::m'.ssSym::(t' ++ [m'.ssSym]))`
	    by (SRW_TAC [][id_thm] THEN
		METIS_TAC [APPEND,APPEND_ASSOC]) THEN
	    Q.EXISTS_TAC `q0'` THEN Q.EXISTS_TAC `ssyms0` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC]
	    ],

      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
      THENL[
	    FIRST_X_ASSUM (Q.SPECL_THEN [`q`,`h a`,`q'`,`[]`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' ((q,[]),a::q',[m'.ssSym]) ((q,h a),q',[m'.ssSym])`
	    by SRW_TAC [][id_thm] THEN
	    Q.EXISTS_TAC `q` THEN
	    Q.EXISTS_TAC `[]` THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC],

	    
	    FIRST_X_ASSUM (Q.SPECL_THEN [`q`,`h a`,`q'`,`h'::t'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' ((q,[]),a::q',h'::(t' ++ [m'.ssSym]))
	    ((q,h a),q',[h'] ++ t' ++ [m'.ssSym])`
	    by SRW_TAC [][id_thm] THEN
	    Q.EXISTS_TAC `q` THEN
	    Q.EXISTS_TAC `h'::t'` THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`q`,`h a`,`q'`,`m'.ssSym::t'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' ((q,[]),a::q',m'.ssSym::(t' ++ [m'.ssSym]))
	    ((q,h a),q',[m'.ssSym] ++ t' ++ [m'.ssSym])`
	    by SRW_TAC [][id_thm] THEN
	    Q.EXISTS_TAC `q` THEN
	    Q.EXISTS_TAC `m'.ssSym::t'` THEN
	    SRW_TAC [][] THEN
	    `m'.ssSym::(t' ++ [m'.ssSym]) = [m'.ssSym]++t' ++ [m'.ssSym]`
	    by SRW_TAC [][] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC]
	    ]
      ]);


val m'StepBufNilH = store_thm
("m'StepBufNilH",
``∀dl p b ssyms'.
ID m' ⊢ dl ◁ ((q,[]),[e],pfx++[m'.ssSym]) → ((p,b),[],ssyms'++[m'.ssSym]) ∧
hInvpda m m' h 
⇒
∃q0 ssyms0.
IDC m' ((q,[]),[e],pfx++[m'.ssSym]) ((q0,h e),[],ssyms0++[m'.ssSym]) ∧
IDC m' ((q0,h e),[],ssyms0++[m'.ssSym]) ((p,b),[],ssyms'++[m'.ssSym])``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [SNOC_APPEND]  THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [ RTC_RULES, RTC_RTC]) THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
SRW_TAC [][] THEN
Cases_on `LAST dl` THEN
Cases_on `q'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
SRW_TAC [][]
 THENL[
       `hInvpda m m' h` by 
       FULL_SIMP_TAC (srw_ss()) [rule1,rule2,rule3,hInvpda, EXTENSION] THEN
       `MEM ((q'',r'),[],sh::st) dl` by METIS_TAC [MEM,MEM_APPEND] THEN
       `∃pf.sh::st = pf ++[m'.ssSym]` by METIS_TAC [z0Inv,memld] THEN
       SRW_TAC [][] THEN
       Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
       THENL[
	     METIS_TAC [memStkSyms],
	     METIS_TAC [memStkSyms],

	     `(q'',r') = (q0,[])` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     `ssyms' = [m.ssSym]` by METIS_TAC [APPEND,APPEND_11] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`q''`,`[]`,`[]`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     `ID m' (m'.start,[],[m'.ssSym]) ((m.start,[]),[],[m.ssSym; m'.ssSym])`
	     by SRW_TAC [][id_thm] THEN
	    Q.EXISTS_TAC `q0` THEN Q.EXISTS_TAC `ssyms0` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES,RTC_RTC],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`b`,`h'::t`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' ((q',b),[],h'::(t ++ [m'.ssSym])) ((p,b),[],ssyms ++ t ++ [m'.ssSym])`
	     by (SRW_TAC [][id_thm] THEN METIS_TAC []) THEN
	     Q.EXISTS_TAC `q0'` THEN Q.EXISTS_TAC `ssyms0`THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [RTC_RULES_RIGHT1,RTC_RTC],

	     FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`isym::b`,`h'::t`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' ((q',isym::b),[],h'::(t ++ [m'.ssSym]))
	     ((p,b),[],ssyms ++ t ++ [m'.ssSym])`
	    by (SRW_TAC [][id_thm] THEN
		METIS_TAC []) THEN
	    Q.EXISTS_TAC `q0'` THEN Q.EXISTS_TAC `ssyms0`THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES_RIGHT1,RTC_RTC],

	    `(q'',r') = (q0,[])` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`q''`,`[]`,`m'.ssSym::t`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m' (m'.start,[],m'.ssSym::(t ++ [m'.ssSym]))
	     ((m.start,[]),[],m.ssSym::m'.ssSym::(t ++ [m'.ssSym]))`	    
	    by (SRW_TAC [][id_thm] THEN
		METIS_TAC [APPEND,APPEND_ASSOC]) THEN
	    Q.EXISTS_TAC `q0` THEN Q.EXISTS_TAC `ssyms0`THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [RTC_RULES_RIGHT1,RTC_RTC]
	    ],

       `hInvpda m m' h` by 
       FULL_SIMP_TAC (srw_ss()) [rule1,rule2,rule3,hInvpda, EXTENSION] THEN
       `∃pf.sh::st = pf ++[m'.ssSym]` by METIS_TAC [z0Inv,memld] THEN
       SRW_TAC [][] THEN
       Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
      THENL[
	    `ssyms'=[]` by METIS_TAC [APPEND_NIL,APPEND_11] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `ID m' ((p,[]),[a],[m'.ssSym]) ((p,h a),[],[m'.ssSym])`
	    by SRW_TAC [][id_thm] THEN
	    IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	    SRW_TAC [][] THEN
	    `p'=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	    Q.EXISTS_TAC `p` THEN
	    Q.EXISTS_TAC `[]` THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [RTC_RULES_RIGHT1,RTC_RTC,ldImprtc2list],

	    `ID m' ((p,[]),[a],h'::(t ++ [m'.ssSym])) 
	    ((p,h a),[],h'::(t ++ [m'.ssSym]))`
	    by SRW_TAC [][id_thm] THEN
	    IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	    SRW_TAC [][] THEN
	    `p'=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	    Q.EXISTS_TAC `p` THEN
	    Q.EXISTS_TAC `h'::t` THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [RTC_RULES_RIGHT1,RTC_RTC,ldImprtc2list],

	    `ID m' ((p,[]),[a],m'.ssSym::(t ++ [m'.ssSym])) 
	    ((p,h a),[],m'.ssSym::(t ++ [m'.ssSym]))`
	    by SRW_TAC [][id_thm] THEN
	    IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	    SRW_TAC [][] THEN
	    `p'=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	    Q.EXISTS_TAC `p` THEN
	    Q.EXISTS_TAC `m'.ssSym::t` THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [RTC_RULES_RIGHT1,RTC_RTC,ldImprtc2list]	    
	    ]]);



val m'ImpmBufInpSame = store_thm
("m'ImpmBufInpSame",
``∀dl q b x pfx.
ID m' ⊢ dl ◁ ((q,b),x,pfx++[m'.ssSym]) → ((p,b'),x,ssyms'++[m'.ssSym]) ∧
q ∈ states m ∧ hInvpda m m' h
⇒
IDC m (q,b,pfx) (p,b',ssyms')``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  METIS_TAC [RTC_RULES]) THEN
`h' = ((q,b),x,pfx ++ [m'.ssSym])` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
IMP_RES_TAC listDerivHdBrk THEN
SRW_TAC [][] THEN
Cases_on `h''` THEN
Cases_on `q'` THEN
 Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
SRW_TAC [][]
THENL[
      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
      THENL[
	    METIS_TAC [memStkSyms],
	    METIS_TAC [memStkSyms],

	    `(q,b) = (q0,[])` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`m.start`,`[]`,`q'`,`[m.ssSym]`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m (q,b,h'::t') (p',b,ssyms ++ t')` by SRW_TAC [][id_thm] THEN
	    METIS_TAC [RTC_RULES],	    

	    `p' ∈ states m` by (SRW_TAC [][states_def, EXTENSION] THEN
				METIS_TAC []) THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`p'`,`b`,`q'`,`ssyms++t'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m (q,b,h'::t') (p',b,ssyms ++ t')` by SRW_TAC [][id_thm] THEN
	    METIS_TAC [RTC_RULES],

	    `p' ∈ states m` by (SRW_TAC [][states_def, EXTENSION] THEN
				METIS_TAC []) THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`p'`,`r'`,`q'`,`ssyms++t'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m (q,isym::r',h'::t') (p',r',ssyms ++ t')` by SRW_TAC [][id_thm] THEN
	    METIS_TAC [RTC_RULES],

	    `(q,b) = (q0,[])` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`m.start`,`[]`,`q'`,`[m.ssSym]`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `ID m (q,b,h'::t') (p',b,ssyms ++ t')` by SRW_TAC [][id_thm] THEN
	    METIS_TAC [RTC_RULES]
	    ],


      Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      (`LENGTH (a::q') ≤ LENGTH q'` by METIS_TAC [ldIdcInpLen] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [])
      ]);



val m'isSuff = store_thm
("m'isSuff",
``∀dl q' b ssyms'.
ID m' ⊢ dl ◁ ((q,[]),[h'],pfx ++ [m'.ssSym]) → ((q',b),[],ssyms' ++ [m'.ssSym]) ∧
hInvpda m m' h 
⇒
isSuffix b (h h')``,
	     
HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [SNOC_APPEND]  THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [ RTC_RULES, RTC_RTC]) THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
SRW_TAC [][] THEN
Cases_on `LAST dl` THEN
Cases_on `q''` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
SRW_TAC [][]
 THENL[
       `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) [rule1,rule2,hInvpda,
						     rule3,EXTENSION] THEN
       `∃pf.sh::st = pf ++[m'.ssSym]` by METIS_TAC [z0Inv,memld] THEN
       SRW_TAC [][] THEN
       Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
       THENL[
	     METIS_TAC [memStkSyms],
	     METIS_TAC [memStkSyms],

	     `(q''',r') = (q0,[])` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     `ssyms' = [m.ssSym]` by METIS_TAC [APPEND_11,APPEND] THEN
	     SRW_TAC [][] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`q'''`,`[]`,`[]`] MP_TAC) THEN
	     SRW_TAC [][],

	     FIRST_X_ASSUM (Q.SPECL_THEN [`q''`,`b`,`h''::t`] MP_TAC) THEN
	     SRW_TAC [][],

	     FIRST_X_ASSUM (Q.SPECL_THEN [`q''`,`isym::b`,`h''::t`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	     FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
	     METIS_TAC [APPEND_ASSOC],

	     `(q''',r') = (q0,[])` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FIRST_X_ASSUM (Q.SPECL_THEN [`q'''`,`[]`,`m'.ssSym::t`] MP_TAC) THEN
	     SRW_TAC [][]
	     ],

       `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) [rule1,rule2,hInvpda,
						     rule3,EXTENSION] THEN
       `∃pf.sh::st = pf ++[m'.ssSym]` by METIS_TAC [z0Inv,memld] THEN
       SRW_TAC [][] THEN
       Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
       THEN1
	     (`ssyms'=[]` by METIS_TAC [APPEND_11,APPEND_NIL] THEN
	     SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	     SRW_TAC [][] THEN
	     `p=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL]) THEN

	     (IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	     SRW_TAC [][] THEN
	     `p=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL])]);
	     

val m'ImpmhTohh' = store_thm
("m'ImpmhTohh'",
``∀dl q' ssyms'.
ID m' ⊢ dl ◁ ((q,[]),[h'],pfx ++[m'.ssSym]) → ((q',h h'),[],ssyms' ++ [m'.ssSym]) ∧
hInvpda m m' h ∧ q ∈ states m
⇒
IDC m (q,[],pfx) (q',[],ssyms')``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [] [SNOC_APPEND]  THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [ RTC_RULES, RTC_RTC]) THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
SRW_TAC [][] THEN
Cases_on `LAST dl` THEN
Cases_on `q''` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,rule3,EXTENSION] THEN
SRW_TAC [][] THEN
 `hInvpda m m' h ` by 
 FULL_SIMP_TAC (srw_ss()) [hInvpda,rule1,rule2,
			   rule3,EXTENSION]
 THENL[
       `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) [rule1,rule2,hInvpda,
						     rule3,EXTENSION] THEN
       `∃pf.sh::st = pf ++[m'.ssSym]` by METIS_TAC [z0Inv,memld] THEN
       SRW_TAC [][] THEN
       Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
       THENL[
	     METIS_TAC [memStkSyms],
	     METIS_TAC [memStkSyms],

	     `ssyms' = [m.ssSym]` by METIS_TAC [APPEND_11, APPEND] THEN
	     SRW_TAC [][] THEN
	     `(q''',r') = (q0,[])` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     `IDC m (q,[],pfx) (q''',[],[])` by METIS_TAC [APPEND,APPEND_NIL] THEN
	     `∃dl.ID m ⊢ dl ◁ (q,[],pfx) → (q''',[],[])`
	     by METIS_TAC [ rtc2list_exists'] THEN
	     Cases_on `LENGTH dl' > 1` THEN1
	     METIS_TAC [memStates] THEN
	     Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     `LENGTH t = 0` by DECIDE_TAC THEN
	     `t=[]` by METIS_TAC [LENGTH_NIL] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [],
	    

	     FIRST_X_ASSUM (Q.SPECL_THEN [`q''`,`h''::t`] MP_TAC) THEN
	     SRW_TAC [][] THEN
	     `ID m (q'',[],h''::t) (p,[],ssyms ++ t)`
	     by SRW_TAC [][id_thm] THEN
	     METIS_TAC [RTC_RULES_RIGHT1],

	     `h''::(t++[m'.ssSym]) = h''::t++[m'.ssSym]` by SRW_TAC [][] THEN
	     `isSuffix (isym::h h') (h h')` by METIS_TAC [m'isSuff] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def, IS_PREFIX_APPEND] THEN
	     `LENGTH (REVERSE (h h')) = LENGTH (REVERSE (h h') ++ [isym] ++ l')`
	     by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],

	     `(q''',r') = (q0,[])` by METIS_TAC [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     `IDC m (q,[],pfx) (q''',[],m'.ssSym::t)` 
	     by METIS_TAC [APPEND,APPEND_NIL] THEN
	     `∃dl.ID m ⊢ dl ◁ (q,[],pfx) → (q''',[],m'.ssSym::t)`
	     by METIS_TAC [ rtc2list_exists'] THEN
	     Cases_on `LENGTH dl' > 1` THEN1
	     METIS_TAC [memStates] THEN
	     Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	     FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     `LENGTH t' = 0` by DECIDE_TAC THEN
	     `t'=[]` by METIS_TAC [LENGTH_NIL] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     ],

       `hInvpda m m' h` by FULL_SIMP_TAC (srw_ss()) [rule1,rule2,hInvpda,
						     rule3,EXTENSION] THEN
       `∃pf.sh::st = pf ++[m'.ssSym]` by METIS_TAC [z0Inv,memld] THEN
       SRW_TAC [][] THEN
       Cases_on `pf` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
       THENL[
	     IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	     SRW_TAC [][] THEN
	     `p=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	     SRW_TAC [][] THEN
	     `ssyms'=[]` by METIS_TAC [APPEND_11,APPEND_NIL] THEN
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     METIS_TAC [m'ImpmBufInpSame,APPEND_NIL],

	     IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	     SRW_TAC [][] THEN
	     `p=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	     SRW_TAC [][] THEN
	     `h''::(t++[m'.ssSym]) = h''::t++[m'.ssSym]` by SRW_TAC [][] THEN
	     METIS_TAC [m'ImpmBufInpSame,APPEND_NIL],

	     IMP_RES_TAC ldIdcInpSuffix THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [isSuffix_def] THEN
	     SRW_TAC [][] THEN
	     `p=[]` by METIS_TAC [APPEND_NIL, APPEND_11] THEN
	     SRW_TAC [][] THEN
	     `m'.ssSym::(t++[m'.ssSym]) = m'.ssSym::t++[m'.ssSym]` by SRW_TAC [][] THEN
	     METIS_TAC [m'ImpmBufInpSame,APPEND_NIL]
	     ]]);


val m'StateImpm = store_thm
("m'StateImpm",
``∀q b i s.
ID m' ⊢ dl ◁ ((q,b),i,s) → ((q',b'),i',s') ∧ hInvpda m m' h ∧ q ∈ states m
⇒
(q' ∈ states m)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 METIS_TAC []) THEN
`h' = ((q,b),i,s)` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
IMP_RES_TAC listDerivHdBrk THEN
SRW_TAC [][] THEN
Cases_on `h''` THEN
Cases_on `q''` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
(FULL_SIMP_TAC (srw_ss()) [rule1,rule2,rule3,EXTENSION,hInvpda] THEN
 RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [states_def, EXTENSION] THEN
 METIS_TAC []));



val m'Impm = store_thm
("m'Impm",
``∀dl q pfx. 
 ID m' ⊢ dl ◁ ((q,[]),x,pfx++[m'.ssSym]) → ((p,[]),[],ssyms'++[m'.ssSym]) ∧ 
stkSymsInPda m pfx ∧ q ∈ states m ∧
 hInvpda (m:(α, β, γ) pda) (m':(α, β, γ # α list) pda) (h: α -> α list) 
 ⇒
 ∃dl'.ID m ⊢ dl' ◁ (q,FLAT (MAP h x),pfx) → (p,[],ssyms')``,

Induct_on `x` THEN
SRW_TAC [][] THEN1
(IMP_RES_TAC m'ImpmNil THEN
 METIS_TAC [rtc2list_exists']) THEN
`ID m' ⊢ dl ◁ ((q,[]),[h']++x,pfx++[m'.ssSym]) → ((p,[]),[],ssyms'++[m'.ssSym])` 
by METIS_TAC [APPEND] THEN
IMP_RES_TAC idTransOnInpPfx THEN
 `IDC m' ((q,[]),[h'],pfx++[m'.ssSym]) (q0,[],ssyms0)`
 by METIS_TAC [idTransOnInpPfxToNil,  rtc2list_exists'] THEN
 `∃p.ssyms0=p++[m'.ssSym]` by METIS_TAC [ rtc2list_exists',z0Inv,memld] THEN
SRW_TAC [][] THEN
 `stkSymsInPda m p'` by METIS_TAC [stkSymsPdaInvm'm] THEN
Cases_on `q0` THEN
`∃q0 ssyms0.IDC m' ((q',r),x,p' ++ [m'.ssSym]) ((q0,[]),x,ssyms0 ++ [m'.ssSym]) ∧
IDC m' ((q0,[]),x,ssyms0 ++ [m'.ssSym]) ((p,[]),[],ssyms' ++ [m'.ssSym])` 
by METIS_TAC [m'StepBufToNil, rtc2list_exists',ldImprtc2list] THEN
`stkSymsInPda m ssyms0` by METIS_TAC [stkSymsPdaInvm'm, RTC_RTC] THEN
`q0 ∈ states m` by METIS_TAC [ RTC_RTC, rtc2list_exists',m'StateImpm] THEN
 `∃dl'.ID m ⊢ dl' ◁ (q0,FLAT (MAP h x),ssyms0) → (p,[],ssyms')`
 by METIS_TAC [rtc2list_exists'] THEN
SRW_TAC [][] THEN
`q' ∈ states m` by METIS_TAC [ RTC_RTC, rtc2list_exists',m'StateImpm] THEN
`IDC m (q',r,p') (q0,[],ssyms0)` by METIS_TAC [m'ImpmBufInpSame, 
					       rtc2list_exists'] THEN
`∃q0 ssyms0.IDC m' ((q,[]),[h'],pfx ++ [m'.ssSym]) 
((q0,h h'),[],ssyms0 ++ [m'.ssSym]) ∧
IDC m' ((q0,h h'),[],ssyms0 ++ [m'.ssSym]) ((q',r),[],p' ++ [m'.ssSym])` 
by METIS_TAC [m'StepBufNilH,rtc2list_exists'] THEN
`q0' ∈ states m` by METIS_TAC [ RTC_RTC, rtc2list_exists',m'StateImpm] THEN
`IDC m (q0',h h',ssyms0') (q',r,p')` by METIS_TAC [m'ImpmBufInpSame,
						   rtc2list_exists'] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC ldImprtc2list THEN
`(ID m)^* (q0',h h',ssyms0') (q0,[],ssyms0)`
by METIS_TAC [RTC_RTC] THEN
`(ID m)^* (q0',h h'++ FLAT (MAP h x),ssyms0') (q0,FLAT (MAP h x),ssyms0)`
by METIS_TAC [idcInpInsert, APPEND_NIL] THEN
`IDC m (q,[],pfx) (q0',[],ssyms0')` by 
METIS_TAC [m'ImpmhTohh',hInvpda,rtc2list_exists'] THEN
METIS_TAC [RTC_RTC,rtc2list_exists',idcInpInsert,APPEND_NIL]);



val m'FstStep = store_thm
("m'FstStep",
``ID m' ⊢ l ◁ (m'.start,x,[m'.ssSym]) → (state,[],stack) ∧
(state ≠ m'.start) ∧ hInvpda m m' h 
⇒
ID m' ⊢ TL l ◁ ((m.start,[]),x,[m.ssSym]++[m'.ssSym]) → (state,[],stack)``,

Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `h'` THEN
Cases_on `q` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [hInvpda, rule1,rule2,rule3,EXTENSION] THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN SRW_TAC [][] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
METIS_TAC [memStkSyms]);


val m'FinState = store_thm
("m'FinState",
``MEM (q,r) m'.final ∧ hInvpda m m' h
⇒
(q,r) ≠ m'.start ∧ (r=[])``,

FULL_SIMP_TAC (srw_ss()) [hInvpda] THEN
SRW_TAC [][] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`q ∈ states m` by SRW_TAC [][states_def] THEN
METIS_TAC []);


val mSsymInm' = store_thm
("mSsymInm'",
``hInvpda m m' h ⇒ stkSymsInPda m' [m.ssSym]``,

SRW_TAC [][hInvpda, rule1,rule2,rule3,memStkSymsEq] THEN
SRW_TAC [][stkSymsInPda] THEN
METIS_TAC [memStkSymsEq,MEM]);


val invhEq = store_thm 
("invhEq",
``∀m m'. hInvpda m m' h
 ⇒ 
 (x ∈ lafs m' = x ∈ { w | (FLAT (MAP h w)) ∈ lafs m })``,

SRW_TAC [][EXTENSION, language_def, EQ_IMP_THM, lafs_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC rtc2list_exists' THEN1

(Cases_on `state` THEN
 IMP_RES_TAC m'FinState THEN
 SRW_TAC [][] THEN
 IMP_RES_TAC m'FstStep THEN
 `q ∈ states m` by (FULL_SIMP_TAC (srw_ss()) [states_def, hInvpda] THEN
		    METIS_TAC []) THEN
 `MEM q m.final` by (FULL_SIMP_TAC (srw_ss()) [states_def, hInvpda] THEN
		     METIS_TAC []) THEN
 `stkSymsInPda m [m.ssSym]` by SRW_TAC [][stkSymsInPda, stkSyms_def] THEN
 `∃pf.stack = pf ++ [m'.ssSym]` by METIS_TAC [memld,z0Inv] THEN
 SRW_TAC [][] THEN
 `m.start ∈ states m` by SRW_TAC [][states_def] THEN
 METIS_TAC [m'Impm, ldImprtc2list]) THEN

Cases_on `LENGTH l > 1`
THENL[
      `m.start ∈ states m` by SRW_TAC [][states_def] THEN
      `stkSymsInPda m' [m.ssSym]` by METIS_TAC [mSsymInm'] THEN
      IMP_RES_TAC mImpm' THEN
      SRW_TAC [][Once RTC_CASES1] THEN
      Q.EXISTS_TAC `(state,[])` THEN
      Q.EXISTS_TAC `stack++[m'.ssSym]` THEN
      SRW_TAC [][] THEN1
      (DISJ2_TAC THEN
       Q.EXISTS_TAC `((m.start,[]),x,[m.ssSym] ++ [m'.ssSym])` THEN
       SRW_TAC [][id_thm] THEN1
       FULL_SIMP_TAC (srw_ss()) [hInvpda, rule3, EXTENSION] THEN
       METIS_TAC [APPEND]) THEN
      FULL_SIMP_TAC (srw_ss()) [hInvpda],

      Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `LENGTH t = 0` by DECIDE_TAC THEN
      `t=[]` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      `(∀e. MEM e x ⇒ (h e = []))` by (SRW_TAC [][] THEN
				       FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
				       SRW_TAC [][] THEN
				       FULL_SIMP_TAC (srw_ss()) [FLAT_APPEND]) THEN
      `m.start ∈ states m` by SRW_TAC [][states_def] THEN
      `stkSymsInPda m' [m.ssSym]` by METIS_TAC [mSsymInm'] THEN
      `IDC m' ((m.start,[]),x,[m.ssSym] ++ [m'.ssSym]) 
              ((m.start,[]),[],[m.ssSym] ++ [m'.ssSym])` 
      by METIS_TAC [mImpm'HNil] THEN
      SRW_TAC [][Once RTC_CASES1] THEN
      Q.EXISTS_TAC `(m.start,[])` THEN
      Q.EXISTS_TAC `[m.ssSym] ++ [m'.ssSym]` THEN
      SRW_TAC [][] THEN1
      (Q.EXISTS_TAC `((m.start,[]),x,[m.ssSym] ++ [m'.ssSym])` THEN
       SRW_TAC [][id_thm] THEN1
       FULL_SIMP_TAC (srw_ss()) [hInvpda, rule3, EXTENSION] THEN
       METIS_TAC [APPEND]) THEN
      FULL_SIMP_TAC (srw_ss()) [hInvpda]
      ]);
 
val _ = export_theory();