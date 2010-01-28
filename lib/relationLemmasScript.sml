(* A theory about grammars *)

open HolKernel boolLib bossLib Parse BasicProvers

open stringTheory relationTheory listTheory arithmeticTheory Defn
containerTheory pred_setTheory rich_listTheory

open pred_setTheory listLemmasTheory containerLemmasTheory setLemmasTheory

 

val _ = new_theory "relationLemmas";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

val rtc2list = Define
    `(rtc2list R [] = F) /\
    (rtc2list R [x] = T) /\
    (rtc2list R (x::y::rst) = R x y /\ rtc2list R (y::rst))`
val _ = export_rewrites ["rtc2list_def"]


val listderiv_def = Define`
  listderiv R d s0 s1 = rtc2list R d /\
                        (HD d = s0) /\
                        (LAST d = s1)`;

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 550),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [BreakSpace(1,1), TOK "⊢",
                                 BreakSpace(1,1), TM, BreakSpace(1,1),
                                 TOK "◁", BreakSpace(1,1),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, BreakSpace(1,1), TOK "→", HardSpace 1],
                  term_name = "listderiv"}



val rtc2list_exists' = store_thm (
"rtc2list_exists'",
  ``!u v. RTC R u v ==> ∃l. R ⊢ l ◁ u → v``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `[u]` THEN SRW_TAC [][listderiv_def],
    `?h t. (l = h::t)` by METIS_TAC [list_CASES, listderiv_def, rtc2list] THEN
    Q.EXISTS_TAC `u::l` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [listderiv_def]
  ]);


val rtc2list_split = store_thm
("rtc2list_split",
  ``rtc2list R l ==> MEM e l ==>
    ?l1 l2.
        rtc2list R (l1 ++ [e]) /\
        rtc2list R (e :: l2) /\
        (l1 ++ [e] ++ l2 = l)``,
  Induct_on `l` THEN SRW_TAC [][] THEN
  Cases_on `l` THEN SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`[]`, `[]`] THEN SRW_TAC [][],
    MAP_EVERY Q.EXISTS_TAC [`[]`, `h::t`] THEN SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [],
    FULL_SIMP_TAC (srw_ss()) [] THENL [
      MAP_EVERY Q.EXISTS_TAC [`[h]`, `t`] THEN SRW_TAC [][],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      MAP_EVERY Q.EXISTS_TAC [`h::l1`, `l2`] THEN
      SRW_TAC [][] THEN
      Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) []
    ]
  ]);


val rtc2list_distrib_append_fst = store_thm
 ("rtc2list_distrib_append_fst",
  ``rtc2list R (l1 ++ l2) /\ ~(l1 = []) ==> rtc2list R l1``,
  Induct_on `l1` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `l1` THEN SRW_TAC [][]);


val rtc2list_distrib_append_snd = store_thm
("rtc2list_distrib_append_snd",
``!l1 l2 R.rtc2list R (l1++l2) ==> ~(l2=[]) ==> rtc2list R l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rtc2list] THEN
Cases_on `l1` THEN METIS_TAC [rtc2list, APPEND])

val rtc2list_append_right = store_thm
("rtc2list_append_right",
 ``!l R v.rtc2list R l ==> R (LAST l) v ==> rtc2list R (l++[v])``,
          Induct_on `l` THEN SRW_TAC [] [rtc2list] THEN
          Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [rtc2list])

val rtc2listRtcRdHdLast = store_thm ("rtc2listRtcRdHdLast",
``!t.rtc2list (rderives ag) t ==> ~(t=[]) ==>
      RTC (rderives ag)(HD t) (LAST t)``,
    Induct_on `t` THEN SRW_TAC [] [rtc2list] THEN
    SRW_TAC [] [RTC_RULES] THEN
    Cases_on `t` THEN
    FULL_SIMP_TAC (srw_ss()) [rtc2list, RTC_RULES] THEN
    METIS_TAC [RTC_RULES])



val rtcRderivesRtc2list = store_thm ("rtcRderivesRtc2list",
``!h h'.RTC (rderives ag) h h' ==>
rtc2list (rderives ag) (h'::dl) ==>
RTC (rderives ag) h (LAST (h'::dl))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [rtc2list]
THENL[
 METIS_TAC [HD, rtc2listRtcRdHdLast, NOT_CONS_NIL],

 `RTC (rderives ag) h'' (LAST (h''::dl))`
     by METIS_TAC [rtc2listRtcRdHdLast, HD, NOT_CONS_NIL] THEN
 METIS_TAC [RTC_RULES, RTC_RTC]]);


val rtc2listRtcHdLast = store_thm ("rtc2listRtcHdLast",
``!t.rtc2list R t ==> ~(t=[]) ==>
   RTC R (HD t) (LAST t)``,
    Induct_on `t` THEN SRW_TAC [] [rtc2list] THEN
    SRW_TAC [] [RTC_RULES] THEN
    Cases_on `t` THEN
    FULL_SIMP_TAC (srw_ss()) [rtc2list, RTC_RULES] THEN
    METIS_TAC [RTC_RULES]);


val rtc2list_mem = store_thm
("rtc2list_mem",
``∀l e1 e2.R ⊢ l ◁ e1 → e2 ∧
    MEM e' l
       ⇒
    R^* e1 e' ∧ R^* e' e2``,

  Induct_on `l` THEN 
  SRW_TAC [][rtc2list, listderiv_def] THEN1      
   METIS_TAC [RTC_RULES] THEN1
   METIS_TAC [HD, rtc2listRtcHdLast, NOT_CONS_NIL] THEN
  Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`LAST (h::t)`] MP_TAC) THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  METIS_TAC [RTC_RULES]);

val listderiv_thm = store_thm(
  "listderiv_thm",
  ``R ⊢ h::t ◁ x → y ⇔ 
    (h = x) ∧
    ((t = []) ∧ (h = y) ∨
     ∃h' t'. (t = h'::t') ∧ R h h' ∧
             R ⊢ t ◁ h' → y)``,
  SRW_TAC [][listderiv_def] THEN Cases_on `t` THEN 
  SRW_TAC [][] THEN 
  METIS_TAC []);



val rtc2listLastFront = store_thm
("rtc2listLastFront",
``∀l.rtc2list R l ∧ (FRONT l≠[]) 
 ⇒ 
 rtc2list R ([LAST (FRONT l)]++[LAST l])``,

SRW_TAC [][] THEN
Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`l = FRONT l ++ [LAST l]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`l = FRONT (FRONT l) ++ ([LAST (FRONT l)]++[LAST l])` by
 METIS_TAC [APPEND_FRONT_LAST,APPEND_ASSOC] THEN
`rtc2list R ([LAST (FRONT l)] ++ [LAST l])` 
 by METIS_TAC [rtc2list_distrib_append_snd,MEM,MEM_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) []);


val listderivNrc = store_thm
("listderivNrc",
``∀l l' x y.R ⊢ l ◁ x → y ∧ LENGTH l < LENGTH l' ⇒
  ∃m.m < LENGTH l' ∧ NRC R m x y``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[
      Q.EXISTS_TAC `0` THEN
      SRW_TAC [][] THEN
      DECIDE_TAC,

      FIRST_X_ASSUM (Q.SPECL_THEN [`TL l'`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `l'=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      RES_TAC THEN
      Q.EXISTS_TAC `SUC m` THEN
      SRW_TAC [][] THEN
      SRW_TAC [][NRC] THEN
      METIS_TAC []]);
      

val nrcListExists = store_thm
("nrcListExists",
``∀x y m.NRC R m x y ⇒ 
 ∃l.R ⊢ l ◁ x → y ∧ (LENGTH l=SUC m)``,

Induct_on `m` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] 
THENL[
      Q.EXISTS_TAC `[x]` THEN
      SRW_TAC [][],

      FULL_SIMP_TAC (srw_ss()) [NRC] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`z`,`y`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `x::l` THEN
      SRW_TAC [][] THEN
      Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []]);


val ldTl = store_thm
("ldTl",
``R ⊢ h::h'::t' ◁ x → y
    ⇒
    R ⊢ h'::t' ◁ h' → y``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def]);



val rtc2listExistsLen = store_thm
("rtc2listExistsLen",
``∀t.rtc2list R t 
	⇒ 
   ∃l. (LENGTH l = LENGTH t) ∧ R ⊢ l ◁ (HD t) → (LAST t)``,

Induct_on `t` THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `h::t` THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]);


val ldMemLast = store_thm
("ldMemLast",
``∀dl x r1 r2.
R ⊢ dl ◁ x → y ∧ (dl= r1++[e]++r2)
⇒
 R ⊢ [e]++r2 ◁ e → y``,

Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq,listderiv_def] THEN
Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
 METIS_TAC [APPEND,APPEND_ASSOC]);


val ldMemRel = store_thm
("ldMemRel",
 ``∀dl x e1 e2 p m s.R ⊢ dl ◁ x → y ∧ (dl = p++[e1]++m++[e2]++s)
 ⇒
 R^* e1 e2``,

Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def,lreseq] THEN
SRW_TAC [][] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`e2`,`[]`,`t'`,`s`] MP_TAC) THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES]) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`e1`,`e2`,`t'`,`m`,`s`] MP_TAC) THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES]);


val listDerivHdBrk = store_thm
("listDerivHdBrk",
``R ⊢ h::h'::t' ◁ x → y ⇒
 R h h' ∧ R ⊢ h'::t' ◁ h' → y``,

SRW_TAC [][listderiv_def]);


val listderivfront = store_thm
("listderivfront",
``∀dl x y.R ⊢ dl ◁ x → y  ⇒ (FRONT dl ≠ []) 
      ⇒
      R ⊢ FRONT dl ◁ x → (LAST (FRONT dl))``,

Induct_on `dl` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_FRONT_LAST,NOT_CONS_NIL,rtc2list_distrib_append_fst,
	   frontAppendFst,HD,APPEND]);


val rtc2listImpLd = store_thm
("rtc2listImpLd",
``∀t. rtc2list R t ⇒ R ⊢ t ◁ HD t → LAST t``,

Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]);

(*
val elId = store_thm
("elId",
``∀n l.n + 1< LENGTH l ⇒ rtc2list p l 
      ⇒
    p ⊢ l ◁ (EL n l) → (EL (n+1) l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC) THEN SRW_TAC [][]
 ) THEN
Q_TAC SUFF_TAC `p ⊢ EL n' l → EL (SUC (SUC n')) (h::l)` THEN1
METIS_TAC [ADD1] THEN
SRW_TAC [][] THEN
`n'+1 < LENGTH l` by DECIDE_TAC THEN
RES_TAC THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
METIS_TAC [elTlEq]);
*)

val _ = export_theory ();