open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory

open listLemmasTheory relationLemmasTheory containerLemmasTheory
     grammarDefTheory pdaDefTheory symbolDefTheory parseTreeTheory

open pdaEqCfgTheory

open gnfTheory laeslafsTheory

val _ = new_theory "homomorphism"


val _ = diminish_srw_ss ["list EQ"];

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
``R ⊢ dl ◁ x → y ⇒ MEM x dl ∧ MEM y dl``,

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


val inpSyms_empty = store_thm(
  "inpSyms_empty",
  ``(inpSyms m = {}) ==> (laes m ⊆ {[]})``,
  SIMP_TAC (srw_ss()) [laes_def, SUBSET_DEF] THEN
  STRIP_TAC THEN
  Q_TAC SUFF_TAC
     `∀id0 id. m ⊢ id0 →* id ⇒
            ∀s0 i0 stk0 s stk.
              (id0 = (s0,i0,stk0)) ∧ (id = (s,[],stk)) ⇒
              (i0 = [])` THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
  Cases_on `id0'` THEN Cases_on `r` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `i0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `stk0` THEN FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [inpSyms_def, EXTENSION] THEN
  METIS_TAC []);


val inpSyms_empty_lafs = store_thm(
  "inpSyms_empty_lafs",
  ``(inpSyms m = {}) ==> (lafs m ⊆ {[]})``,
  SIMP_TAC (srw_ss()) [lafs_def, SUBSET_DEF] THEN
  STRIP_TAC THEN
  Q_TAC SUFF_TAC
     `∀id0 id. m ⊢ id0 →* id ⇒
            ∀s0 i0 stk0 s stk.
              (id0 = (s0,i0,stk0)) ∧ (id = (s,[],stk)) ∧ s ∈ m.final ⇒
              (i0 = [])` THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
  Cases_on `id0'` THEN Cases_on `r` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `i0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `stk0` THEN FULL_SIMP_TAC (srw_ss()) [ID_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [inpSyms_def, EXTENSION] THEN
  METIS_TAC []);



val rule1 = Define `
  rule1 (m:(α, β, γ) pda) (h: α -> α list) =
    { ((NONE:α option,ssym,q,x),(p,x),ssyms) |
      ∃a. a ∈ inpSyms m ∧ isSuffix x (h a) ∧
          MEM ((NONE,ssym,q),(p,ssyms)) m.next
    }`;

val rule2 = Define `
  rule2 (m:(α, β, γ) pda) (h: α -> α list) =
   { ((NONE:α option,ssym,(q,isym::x)),((p,x),ssyms)) |
     ∃a. a ∈ inpSyms m ∧ isSuffix (isym::x) (h a) ∧
         MEM ((SOME isym,ssym,q),(p,ssyms)) m.next
   }`;

val rule3 = Define `
  rule3 (m:(α, β, γ) pda) (h: α -> α list) newssym=
    { ((SOME a,ssym,(q,[]:α list)),((q,h a),[ssym])) | a,ssym,q |
      a ∈ inpSyms m ∧ q ∈ states m ∧ ssym ∈ (stkSyms m ∪ {newssym}) ∧
      h a ∈ IMAGE h {a}
    }`;

val hInvpda = Define `
  hInvpda (m:(α, β, γ) pda) (m':(α, β, γ # α list) pda) (h: α -> α list) =
    ∃z0. z0 ∉ stkSyms m ∧ (m'.ssSym = z0) ∧
         ∃q0. q0 ∉ states m ∧ (m'.start = (q0,[]:α list)) ∧
              (∀q r.MEM (q,r:α list) m'.final = MEM q m.final ∧ (r=[])) ∧
              ∀r.
                MEM r m'.next ⇔
                r ∈ (rule1 m h ∪ rule2 m h ∪ rule3 m h m'.ssSym) ∪
                     { ((NONE,m'.ssSym,m'.start),
                        ((m.start,[]), [m.ssSym;m'.ssSym])) }
`;

val memMRule1 = store_thm (
  "memMRule1",
  ``MEM ((NONE,sh,q),p,st') m.next ∧ hInvpda m m' h ∧ isSuffix x (h a) ∧
    a ∈ inpSyms m ⇒
    MEM ((NONE,sh,q,x),(p,x),st') m'.next``,
  SRW_TAC [][hInvpda] THEN ASM_SIMP_TAC (srw_ss()) [GSYM DISJ_ASSOC] THEN
  DISJ1_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [rule1] THEN
  METIS_TAC []);

val mImpm'Trans1 = store_thm (
  "mImpm'Trans1",
  ``MEM ((NONE,sh,q),p,st') m.next ∧ hInvpda m m' h ∧ a ∈ inpSyms m
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
``MEM ((SOME ih,sh,q),p,st') m.next ∧ (h a = ih::isyms) ∧ hInvpda m m' h ∧
  a ∈ inpSyms m
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
``∀dl p isyms ssyms'.
     ID m ⊢ dl ◁ (q,h a,ssyms) → (p,isyms,ssyms') ∧
     LENGTH dl > 1 ∧ a ∈ inpSyms m ∧
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
      METIS_TAC [ RTC_RULES_RIGHT1]
]);


val mImpm'InpNil = store_thm
("mImpm'InpNil",
``∀dl q ssyms p.
     ID m ⊢ dl ◁ (q,[],ssyms) → (p,[],ssyms') ∧ hInvpda m m' h ∧
     ~(lafs m ⊆ {[]})
   ⇒
     IDC m' ((q,[]),[],ssyms) ((p,[]),[],ssyms')``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `h'` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [id_thm] THEN
SRW_TAC [][] THEN
`inpSyms m ≠ {}` by METIS_TAC [inpSyms_empty_lafs] THEN
`∃a. a ∈ inpSyms m` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
`isSuffix [] (h a)` by SRW_TAC [][isSuffix_def] THEN
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

val mImpm'HNil = store_thm
("mImpm'HNil",
``∀l1.
hInvpda m m' h  ∧ (∀e. MEM e l1 ⇒ e ∈ inpSyms m) ∧ 
(∀e.MEM e l1 ⇒ (h e = [])) ∧ (q ∈ states m) ∧
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
       FULL_SIMP_TAC (srw_ss()) [],

       Q.EXISTS_TAC `((q,[]),t,h''::(t'++[m'.ssSym]))` THEN
       SRW_TAC [][id_thm] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `hInvpda m m' h`
       by FULL_SIMP_TAC (srw_ss()) [rule1,rule2,rule3,EXTENSION,hInvpda] THEN1
       METIS_TAC [ stkSymsInPda,stkSymsPdaInv,MEM,memStkSyms,
		  memStksymsm']
       ]);


val mImpm' = store_thm
("mImpm'",
``∀x dl q ssyms.ID m ⊢ dl ◁ (q,FLAT (MAP h x),ssyms) → (p,[],ssyms') ∧ 
¬(lafs m ⊆ {[]}) ∧ (∀e. e ∈ x ⇒ e ∈ inpSyms m) ∧
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

val GSPEC_IMAGE = store_thm(
  "GSPEC_IMAGE",
  ``GSPEC f = IMAGE (FST o f) { x | SND (f x) }``,
  SRW_TAC [][EXTENSION, GSPECIFICATION, SPECIFICATION] THEN
  EQ_TAC THEN SRW_TAC [][] THEN Q.EXISTS_TAC `x'` THEN SRW_TAC [][] THEN
  Cases_on `f x'` THEN FULL_SIMP_TAC (srw_ss()) []);

val f2GSPEC = prove(
  ``(\x. p x) = GSPEC (S $, p)``,
  SRW_TAC [][EXTENSION, GSPECIFICATION] THEN SRW_TAC [][SPECIFICATION])

val uc2GSPEC = prove(
  ``UNCURRY (\a b. p a b) = GSPEC (UNCURRY (S (S o ($o $,) o $,) p))``,
  SIMP_TAC (srw_ss()) [EXTENSION, GSPECIFICATION, pairTheory.EXISTS_PROD,
                       pairTheory.FORALL_PROD] THEN
  SRW_TAC [][SPECIFICATION]);

open boolSimps
val lemma =
  SIMP_RULE (srw_ss()) [] (Q.INST [`P` |-> `λl0. h::l = l0 ++ m`]
                                  EXISTS_LIST);

val suffixes_are_finite = store_thm(
  "suffixes_are_finite",
  ``∀l. FINITE { m | isSuffix m l }``,
  SIMP_TAC (srw_ss()) [isSuffix_APPEND] THEN
  Induct_on `l` THEN SRW_TAC [][lemma, GSPEC_OR]);

val PAIR_ABS = prove(
  ``(\x. f x) = (λ(a,b). f (a,b))``,
  SIMP_TAC (srw_ss())[FUN_EQ_THM, pairTheory.FORALL_PROD]);

val FINITE_isSuffixTrans = store_thm(
  "FINITE_isSuffixTrans",
  ``FINITE {((opt,q,r,x),(q',x),r') | (x,a:α) | a ∈ inpSyms (m:(α, β, γ) pda) ∧ 
            isSuffix x ((h:α -> α list) a)}``,

 ONCE_REWRITE_TAC [GSPEC_IMAGE] THEN
  MATCH_MP_TAC IMAGE_FINITE THEN
  SRW_TAC [][PAIR_ABS] THEN
  MATCH_MP_TAC SUBSET_FINITE_I THEN
  Q.EXISTS_TAC `(BIGUNION (IMAGE (\a:α. { l | a ∈ inpSyms m ∧ isSuffix l ((h:α -> α list) a)}) (inpSyms m)))
                   CROSS
                (inpSyms m)` THEN
  Tactical.REVERSE (SRW_TAC [DNF_ss][SUBSET_DEF]) THEN1 METIS_TAC [] THEN
  SRW_TAC [][suffixes_are_finite, finiteInpSyms]);

val GSPEC' = REWRITE_RULE [SPECIFICATION] GSPECIFICATION

val GSPEC_AND = prove(
  ``{ x | p x /\ q x } = {x | p x} ∩ {x | q x}``,
  SRW_TAC [][EXTENSION])

val uc1_gs = prove(
  ``UNCURRY (\x. GSPEC (f x)) =
    GSPEC (UNCURRY (S (S o ($o $,) o $,) (combin$C $IN o GSPEC o f)))``,
  SIMP_TAC (srw_ss()) [EXTENSION, pairTheory.FORALL_PROD, GSPECIFICATION,
                       pairTheory.EXISTS_PROD] THEN
  SRW_TAC [][SPECIFICATION, GSPEC'])


val UNCURRY' = prove(
  ``UNCURRY f = \v. f (FST v) (SND v)``,
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD,FUN_EQ_THM]
  )

val FINITE_INTER2 = store_thm(
  "FINITE_INTER2",
  ``FINITE s2 ⇒ FINITE (s1 ∩ s2)``,
  METIS_TAC [INTER_FINITE, INTER_COMM])

val FINITE_rule1 = store_thm("FINITE_rule1",
  ``FINITE (rule1 (m:(α, β, γ) pda) (h: α -> α list))``,

SRW_TAC [][rule1] THEN
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
Q.ABBREV_TAC `
  (f:(α, β, γ) trans -> (α, β, γ # α list) trans -> bool) =
   \r. case r of
         ((NONE,ssym,q),p,ssyms) =>
           if (∃a x. a ∈ inpSyms m ∧ isSuffix x (h a) ∧ ((NONE,ssym,q),p,ssyms) ∈ m.next)
           then
             { ((NONE:α option,ssym,q,x),(p,x),ssyms) | x, a |
               a ∈ inpSyms m ∧ isSuffix x (h a)
             }
           else {}
       | otherwise => {}
` THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f  (set m.next))` THEN
ASM_SIMP_TAC (srw_ss()) [] THEN1

(ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
              [EXISTS_rule, pairTheory.FORALL_PROD, Abbr`f`] THEN
 Q.X_GEN_TAC `v` THEN Cases_on `v` THEN SRW_TAC [][] THEN
 METIS_TAC [FINITE_isSuffixTrans]) THEN

ONCE_REWRITE_TAC [EXTENSION] THEN
ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [Abbr`f`, Abbr`Horrible`] THEN
ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [pairTheory.FORALL_PROD,
                                   pairTheory.EXISTS_PROD,
                                   EXISTS_OPTION] THEN
SIMP_TAC (srw_ss() ++ COND_elim_ss ++ DNF_ss ++ CONJ_ss) [] THEN
METIS_TAC []);

val FINITE_rule2 = store_thm(
  "FINITE_rule2",
  ``FINITE (rule2 (m:(α, β, γ) pda) (h: α -> α list))``,

SRW_TAC [][rule2] THEN
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
Q.ABBREV_TAC `
  (f:(α, β, γ) trans -> (α, β, γ # α list) trans -> bool) =
  \r. case r of
        ((SOME isym,ssym,q),p,ssyms) =>
           if (∃a x. a ∈ inpSyms m ∧ isSuffix (isym::x) (h a) ∧
                     ((SOME isym,ssym,q),p,ssyms) ∈ m.next)
           then
             { ((NONE:α option,ssym,q,isym::x),(p,x),ssyms) | x, a|
               a ∈ inpSyms m ∧ isSuffix (isym::x) (h a)
             }
           else {}
      | otherwise => {}
` THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f  (set m.next))` THEN
ASM_SIMP_TAC (srw_ss()) [] THEN1
   (ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                 [pairTheory.FORALL_PROD, Abbr`f`] THEN
    ASM_SIMP_TAC (srw_ss()) [FORALL_OPTION] THEN
    SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [GSPEC_IMAGE] THEN
    MATCH_MP_TAC IMAGE_FINITE THEN
    SRW_TAC [][PAIR_ABS] THEN
    MATCH_MP_TAC SUBSET_FINITE_I THEN
    Q.EXISTS_TAC `
      (BIGUNION (IMAGE (\a. { l | isSuffix (x::l) (h a)}) (inpSyms m)))
                   CROSS
      (inpSyms m)` THEN
    Tactical.REVERSE (SRW_TAC [DNF_ss][SUBSET_DEF]) THEN1 METIS_TAC [] THEN
    SRW_TAC [][finiteInpSyms] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN
    Q.X_GEN_TAC `v` THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC SUBSET_FINITE_I THEN
    Q.EXISTS_TAC `{l | isSuffix l (h v)}` THEN CONJ_TAC THEN1
    SRW_TAC [][suffixes_are_finite] THEN
    SIMP_TAC (srw_ss()) [SUBSET_DEF, isSuffix_APPEND] THEN
    SRW_TAC [][] THEN SRW_TAC [][] THEN Q.EXISTS_TAC `l0 ++ [x]` THEN
    METIS_TAC [APPEND, APPEND_ASSOC]) THEN

ONCE_REWRITE_TAC [EXTENSION] THEN
ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [Abbr`f`, Abbr`Horrible`] THEN
ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [pairTheory.FORALL_PROD,
                                   pairTheory.EXISTS_PROD,
                                   EXISTS_OPTION] THEN
SIMP_TAC (srw_ss() ++ COND_elim_ss ++ DNF_ss ++ CONJ_ss) [] THEN
METIS_TAC []);

val FINITE_rule3 = store_thm(
  "FINITE_rule3",
  ``FINITE (rule3 (m:(α, β, γ) pda) (h: α -> α list) newssym)``,

  SRW_TAC [][rule3] THEN
  ONCE_REWRITE_TAC [GSPEC_IMAGE] THEN
  SRW_TAC [][PAIR_ABS] THEN
  MATCH_MP_TAC IMAGE_FINITE THEN
  MATCH_MP_TAC SUBSET_FINITE_I THEN
  Q.EXISTS_TAC `(inpSyms m) × ((newssym INSERT stkSyms m) × states m)`  THEN
  SRW_TAC [][finiteStkSyms, finiteStates] THEN
  SRW_TAC [][SUBSET_DEF] THEN SRW_TAC [][finiteInpSyms]);

val FINITE_finalStateSet = store_thm("FINITE_finalStateSet",
``FINITE {(q,[]:(α, β) symbol list) | q ∈ m.final}``,
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
Q.ABBREV_TAC `f = \q. if (q ∈ m.final) then {(q,[]:(α, β) symbol list)} else {}` THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f (set m.final))` THEN1
SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
            boolSimps.CONJ_ss][EXISTS_rule,
                               Abbr`f`] THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
            boolSimps.CONJ_ss][EXISTS_rule, Abbr`Horrible`, Abbr`f`]);


val exists_hInvpda = store_thm ("exists_hInvpda",
  ``INFINITE univ(:γ) ∧ INFINITE univ(:δ) ⇒
    ∀(m: ((α, β) symbol, γ, δ) pda) h. ∃m'. hInvpda m m' h``,

  SRW_TAC [][hInvpda] THEN
  `FINITE (stkSyms m)`
       by METIS_TAC [finiteStkSyms, FINITE_LIST_TO_SET] THEN
  `∃x0. x0 ∈ (univ((:γ) :γ itself)) ∧ ~(x0 ∈ (stkSyms m))`
      by METIS_TAC [IN_INFINITE_NOT_FINITE, new_ssym_exists] THEN
  `FINITE (set (statesList m))` by SRW_TAC [][] THEN
  `∃q0. q0 ∉ states m`
     by METIS_TAC [new_state_exists, states_list_eqresult] THEN
  `FINITE ((rule1 m h ∪ rule2 m h ∪ rule3 m h x0) ∪
           { ((NONE,x0,(q0,[])),((m.start,[]),[m.ssSym;x0])) })`
     by METIS_TAC [FINITE_rule3, FINITE_rule2, FINITE_rule1, FINITE_UNION,
                   FINITE_SING] THEN
  `∃r. set r =  ((rule1 m h ∪ rule2 m h ∪ rule3 m h x0) ∪
                { ((NONE,x0,(q0,[])),((m.start,[]),[m.ssSym;x0])) })`
     by METIS_TAC [listExists4Set] THEN
  `FINITE {(q,[]:(α, β) symbol list) | q ∈ m.final}`
     by METIS_TAC [FINITE_finalStateSet] THEN
  `∃f. set f = {(q,[]:(α, β) symbol list) | q ∈ m.final}`
     by METIS_TAC [listExists4Set] THEN
  Q.EXISTS_TAC `pda (q0,[]) x0 r f` THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  METIS_TAC []
);

val inverseHomomorphism = Define
`inverseHomomorphism h g = 
{ (MAP ts2str w) | (FLAT (MAP h w)) ∈ language g}`;


val languageWords = Define `
     languageWords g =
     {MAP ts2str tsl | (derives g)^* [NTS (startSym g)] tsl ∧ isWord tsl}`;


fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val invhEq = store_thm
("invhEq",
``∀m m'. hInvpda m m' h ∧ ¬(lafs m ⊆ {[]}) 
 ⇒
 ∀x. (x ∈ lafs m' = 
  x ∈ { w | (FLAT (MAP h w)) ∈ lafs m})``,
MAGIC);
(*
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

Cases_on `LENGTH l > 1` THEN1
MAGIC THEN1
MAGIC
THENL[
 
      `m.start ∈ states m` by SRW_TAC [][states_def] THEN
      `stkSymsInPda m' [m.ssSym]` by METIS_TAC [mSsymInm'] THEN
      `∀e. e ∈ x ⇒ e ∈ inpSyms m` by MAGIC THEN
      `m' ⊢
         ((m.start,[]),x,[m.ssSym] ++ [m'.ssSym]) →*
             ((state,[]),[],stack ++ [m'.ssSym])` by METIS_TAC [mImpm'] THEN
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

      `∀e. e ∈ x ⇒ e ∈ inpSyms m` by MAGIC THEN
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
*)

val ntsTsTypeExists = store_thm("ntsTsTypeExists",
``∀tsl.isWord (tsl :
           (('state # ('nts, 'ts) symbol list) #
            ('nts, 'ts) symbol # 'state # ('nts, 'ts) symbol list, 'ts)
           symbol list) ⇒ 
∃(w :('nts, 'ts) symbol list). (MAP ts2str tsl = MAP ts2str w) ∧ isWord w``,

Induct_on `tsl` THEN SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [ts2str_def, isTmnlSym_def] THEN
Q.EXISTS_TAC `TS t::w` THEN
SRW_TAC [][ts2str_def, isTmnlSym_def]);


val type_thm1 = store_thm("type_thm1",
``∀x y.(derives g)^* x (y:(('state # ('nts, 'ts) symbol list) #
            ('nts, 'ts) symbol # 'state # ('nts, 'ts) symbol list, 'ts) symbol list)
 ⇒ isWord y ⇒ (MAP ts2str y = MAP ts2str (w:('nts,'ts) symbol list)) ⇒
∃y'. 
isWord y' ∧ (MAP ts2str w = MAP ts2str y') ∧ (derives g)^* x y'``,

HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [][] THEN1
METIS_TAC [RTC_DEF] THEN
RES_TAC THEN
Q.EXISTS_TAC `y'` THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_CASES1]);


val invHomomorphismThm = store_thm("invHomomorphismThm",
``∀g (h:('nts, 'ts) symbol -> ('nts, 'ts) symbol list).
    INFINITE (UNIV:'nts set) ∧
    INFINITE (UNIV:'state set) ∧     
    [] ∉ language (g:('nts,'ts) grammar) ∧
    (language g ≠ {}) ⇒
    ∃g':(('state # ('nts, 'ts) symbol list) #
   ('nts, 'ts) symbol # 'state # ('nts, 'ts) symbol list, 'ts) grammar. 
      (languageWords g') = (inverseHomomorphism h g)``,

SRW_TAC [][] THEN
`∃g'.isGnf g' ∧ (language g = language g')` by METIS_TAC [gnfExists] THEN
`∃(m:(('nts, 'ts) symbol, ('nts,'ts) symbol, 'state) pda). 
            (∀x. x ∈ language g = x ∈ laes m)` by METIS_TAC [thm5_3] THEN

`INFINITE (UNIV:('nts, 'ts) symbol set)` by MAGIC THEN                                    
(*
INJECTIVE_IMAGE_FINITE SUBSET_FINITE_I
*)

`∃m':(('nts, 'ts) symbol, ('nts,'ts) symbol, 'state) pda. 
                                   laes m = lafs m'` by METIS_TAC [thm52] THEN
`∃m'':(('nts, 'ts) symbol, ('nts, 'ts) symbol, 'state # ('nts, 'ts) symbol list) pda.
     hInvpda m' m'' h` by METIS_TAC [exists_hInvpda] THEN

`INFINITE (UNIV:('state # ('nts, 'ts) symbol list ) set)` by SRW_TAC [][] THEN

`∃m''':(('nts, 'ts) symbol, ('nts, 'ts) symbol,'state # ('nts, 'ts) symbol list) pda. 
lafs m'' = laes m'''` by METIS_TAC [thm51] THEN

`¬(lafs m' ⊆ {[]})` by (SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC []) THEN

`∃g'':(('state # ('nts, 'ts) symbol list) #
   ('nts, 'ts) symbol # ('state # ('nts, 'ts) symbol list), 'ts) grammar. 
pda2grammar m''' g''` by METIS_TAC [p2gGrExists] THEN
`∀x. x ∈ {w | FLAT (MAP h w) ∈ lafs m'} ⇔ x ∈ lafs m''` by METIS_TAC [invhEq] THEN
Q.EXISTS_TAC `g''` THEN
SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
            boolSimps.CONJ_ss]
[EXISTS_rule, languageWords, inverseHomomorphism, EXTENSION, EQ_IMP_THM] THENL[

`∃w: ('nts, 'ts) symbol list . isWord w ∧ 
(MAP ts2str tsl = MAP ts2str w)` by METIS_TAC [ntsTsTypeExists] THEN
Q.EXISTS_TAC `w`  THEN
SRW_TAC [][] THEN
`∃p.(ID m''')^* (m'''.start,w,[m'''.ssSym]) (p,[],[])` by MAGIC THEN
(* by METIS_TAC [p2gEqPda] *)
`w ∈ laes m'''` by (SRW_TAC [][laes_def] THEN METIS_TAC []) THEN
`w ∈ lafs m''` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [],


`∃tsl:(('state # ('nts, 'ts) symbol list) #
    ('nts, 'ts) symbol # 'state # ('nts, 'ts) symbol list, 'ts) symbol
   list. isWord tsl ∧ (MAP ts2str tsl = MAP ts2str w)` by MAGIC THEN
Q.EXISTS_TAC `tsl`  THEN
SRW_TAC [][] THEN
`w ∈ lafs m''` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
`w ∈ laes m'''` by METIS_TAC [] THEN
`∃p. m''' ⊢ (m'''.start,w,[m'''.ssSym]) →* (p,[],[])`
by (FULL_SIMP_TAC (srw_ss()) [laes_def, EXTENSION] THEN METIS_TAC []) THEN
MAGIC]);
(*`(derives g'')^* [NTS (startSym g'')] w` by METIS_TAC [p2gEqPda] THEN*)




val _ = export_theory();
