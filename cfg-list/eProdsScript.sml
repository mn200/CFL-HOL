(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory arithmeticTheory relationTheory listTheory;
open pred_setTheory grammarDefTheory;

val _ = new_theory "eProds";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

val nullable = Define `nullable g sl = RTC (derives g) sl []`;

val munge0 = Define `
(munge0 g [] = [[]]) ∧
(munge0 g (s::sl) = 
if nullable g [s] then ((MAP (CONS s) (munge0 g sl)) ++ munge0 g sl) 
else (MAP (CONS s) (munge0 g sl)))`;

val munge = Define 
`(munge g p = { rule l r' | ∃r.MEM (rule l r) p ∧ MEM r' (munge0 g r) ∧ ~(r'=[]) })`;

val negr = Define 
`negr g g' = (∀e.MEM e (rules g') = 
e ∈ {rule l r | (rule l r) ∈ (munge g (rules g))}) ∧
(startSym g' =  startSym g)`;

val negr_exists = store_thm
("negr_exists",
``∀g.∃g'.negr g g'``,

SRW_TAC [][negr] THEN
MAGIC);

val eq_snegr = store_thm("eq_snegr",
``negr g g' ⇒ (startSym g = startSym g')``,
Cases_on `g` THEN METIS_TAC [startSym_def,negr]);

(*∧ ∃l.rule l l2 IN munge g (rules g) ∧ rule l l1 IN rules g`;*)
val no_rhs = Define `no_rhs g l1 l2 = MEM l2 (munge0 g l1)`;

val no_rule = Define `no_rule g (rule l1 r1) (rule l2 r2) = (l1=l2) ∧ 
    (MEM r2 (munge0 g r1)) `;

val negr_r1 = prove(
``∀rhs' rhs.(MEM rhs' (munge0 g rhs) ⇒ RTC (derives g) rhs rhs')``,
Induct_on `rhs` THENL
[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [munge0,derives_def] THEN
METIS_TAC [RTC_RULES],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [munge0] THEN
Cases_on `nullable g [h]` THENL
[
FULL_SIMP_TAC (srw_ss()) [MEM] THENL
	[	
	`∃e.MEM e (munge0 g rhs) ∧ (rhs'= (h::e))` by METIS_TAC [MEM_MAP]  THEN
	`RTC (derives g) rhs e` by METIS_TAC [] THEN
	METIS_TAC [rtc_derives_same_append_left,APPEND] ,

	RES_TAC THEN
	FULL_SIMP_TAC (srw_ss()) [nullable] THEN
	METIS_TAC [derives_append,APPEND]
	],

FULL_SIMP_TAC (srw_ss()) [MEM] THEN
`∃e.MEM e (munge0 g rhs) ∧ (rhs'= (h::e))` by METIS_TAC [MEM_MAP]  THEN
METIS_TAC [rtc_derives_same_append_left,APPEND] ]]);

val negr_r2 = prove(
``negr g g' ⇒ derives g' u v ⇒ RTC (derives g) u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [negr,rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [munge] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
IMP_RES_TAC negr_r1 THEN
`derives g [NTS l] r'` by METIS_TAC [res1] THEN
METIS_TAC [rtc_derives_same_append_left,rtc_derives_same_append_right,
	   RTC_RULES]);


val negr_r3 = store_thm("negr_r3",
``∀u v.RTC (derives g') u v ⇒ negr g g' ⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [] [RTC_RULES]  THEN
METIS_TAC [RTC_RTC,negr_r2]
);

val negr_r4 = prove(
``MEM (rule l r) (rules g) ⇒ negr g g' ⇒
(∀r'.MEM r' (munge0 g r) ⇒ ~(r'=[]) ⇒  MEM (rule l r') (rules g'))``,
SRW_TAC [] [negr,rules_def,munge] THEN
METIS_TAC []);


val negr_r5 = store_thm("negr_r5",
``∀rhs.MEM rhs (munge0 g rhs)``,
Induct_on `rhs` THENL[
FULL_SIMP_TAC (srw_ss()) [munge0],
FULL_SIMP_TAC (srw_ss()) [munge0] THEN
Cases_on `nullable g [h]` THENL
[
	FULL_SIMP_TAC (srw_ss()) [] THEN
	DISJ1_TAC THEN
	METIS_TAC [MEM_MAP],

	FULL_SIMP_TAC (srw_ss()) [] THEN
	METIS_TAC [MEM_MAP]]]);

val negr_r6 = prove(
``MEM (rule l r) (rules g) ⇒ ~(r'=[]) ⇒ no_rhs g r r' ⇒ negr g g' ⇒
MEM (rule l r') (rules g')``,

SRW_TAC [] [negr,rules_def,munge,no_rhs] THEN
METIS_TAC []
);

val negr_r7 = prove(
``negr g g' ⇒ 
derives g [NTS s] v ⇒ no_rhs g v v' ⇒ ~(v'=[])  ⇒ derives g' [NTS s] v'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [no_rhs,derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`v'`,`s`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [negr,rules_def,munge] THEN
`(s1=[]) ∧ (s2=[]) ∧ (lhs = s)` by METIS_TAC [slres,slres2] THEN
`MEM (rule s rhs) (rules g)` by METIS_TAC [] THEN
`s1++rhs++s2=rhs` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);


val negr_r8 = prove(
``negr g g' ⇒
derives g u v ⇒ (u=[NTS x]) ⇒ no_rhs g v v' ⇒ ~(v'=[]) ⇒ RTC (derives g') u v'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [no_rhs] THEN
METIS_TAC [RTC_RULES_RIGHT1,negr_r7,no_rhs]);

val negr_r9 = prove(
``~nullable g s ⇒ ∀s'.RTC (derives g) s s' ⇒ ~(s'=[])``,
SRW_TAC [] [nullable]);


val negr_r10 = store_thm("negr_r10",
``~nullable g s ⇒ RTC (derives g) s s' ⇒ ~(s'=[])``,
METIS_TAC [negr_r9]);


val negr_r11 = prove(
``MEM sf (munge0 g s) ∧ ~(sf=[]) ⇒ ∃l.MEM (rule l s) (rules g) ⇒ negr g g' ⇒
MEM (rule l sf) (rules g')``,
SRW_TAC [] [negr,rules_def,munge] THEN
METIS_TAC []);


val negr_r12a = prove(
``∀s1 s1' s2 s2'.no_rhs g s1 s1' ⇒ no_rhs g s2 s2' ⇒ no_rhs g (s1++s2) (s1'++s2')``,
SIMP_TAC (srw_ss()) [no_rhs] THEN
Induct_on `s1` THENL[
 FULL_SIMP_TAC (srw_ss()) [munge0],
 SRW_TAC [] [munge0, MEM_MAP] THEN  SRW_TAC [] []]);

val negr_r12b = prove(
``∀s1 s1' s2 s2'.no_rhs g s1 s1' ⇒ no_rhs g s2 s2' ⇒ no_rhs g s3 s3' ⇒ no_rhs g (s1++s2++s3) (s1'++s2'++s3')``,
SIMP_TAC (srw_ss()) [no_rhs] THEN
Induct_on `s1` 
THENL [
  Induct_on `s2` 
  THENL[
    FULL_SIMP_TAC (srw_ss()) [munge0],
    FULL_SIMP_TAC (srw_ss()) [munge0] THEN Cases_on `nullable g [h]` THEN SRW_TAC [] [munge0, MEM_MAP] THEN SRW_TAC [] [] THEN
    FULL_SIMP_TAC (srw_ss()) [munge0,MEM_MAP]
  ],    
  FULL_SIMP_TAC (srw_ss()) [munge0,MEM_MAP] THEN Cases_on `nullable g [h]`
  THENL [
    FULL_SIMP_TAC (srw_ss()) [MEM_MAP,munge0] THEN SRW_TAC [] []
    THENL [
       SRW_TAC [] [MEM_MAP,munge0],
       SRW_TAC [] [MEM_MAP,munge0]
    ],
    FULL_SIMP_TAC (srw_ss()) [MEM_MAP,munge0] THEN SRW_TAC [] [] THEN SRW_TAC [] [munge0, MEM_MAP] 
  ]]
);


val negr_r13 = prove(
``∀s s'.no_rhs g s s' ⇒ (∃s1 s2 s1' s2'. (s=s1++s2) ∧ (s'=s1'++s2') ⇒ no_rhs g s1 s1' ∧ no_rhs g s2 s2')``,
SIMP_TAC (srw_ss()) [no_rhs] THEN
Induct_on `s` THENL [
  SRW_TAC [] [] THEN
  MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`[]`,`[]`] THEN
  FULL_SIMP_TAC (srw_ss()) [munge0],
  SRW_TAC [] [] THEN
  METIS_TAC [munge0]]);


val negr_r14 = prove(
``∀s1 s2 s'.no_rhs g (s1++s2) s' ⇒ 
		     (∃s1' s2'. (s'=s1'++s2') ∧  no_rhs g s1 s1' ∧ no_rhs g s2 s2')``,
SIMP_TAC (srw_ss()) [no_rhs] THEN
Induct_on `s1` THENL [
  SRW_TAC [] [munge0],
  SRW_TAC [] [munge0, MEM_MAP] THENL [ `∃s1' s2'.
              (y = s1' ++ s2') ∧ MEM s1' (munge0 g s1) ∧
              MEM s2' (munge0 g s2)` by METIS_TAC [] THEN MAP_EVERY Q.EXISTS_TAC [`h::s1'`,`s2'`] THEN SRW_TAC [] [],
				  `∃s1' s2'.
              (s' = s1' ++ s2') ∧ MEM s1' (munge0 g s1) ∧
              MEM s2' (munge0 g s2)` by METIS_TAC [] THEN MAP_EVERY Q.EXISTS_TAC [`s1'`,`s2'`] THEN SRW_TAC [] [],
	`∃s1' s2'.
              (y = s1' ++ s2') ∧ MEM s1' (munge0 g s1) ∧
              MEM s2' (munge0 g s2)` by METIS_TAC [] THEN MAP_EVERY Q.EXISTS_TAC [`h::s1'`,`s2'`] THEN SRW_TAC [] []
]]);


val negr_r15 = store_thm
("negr_r15",
 ``∀s sf.RTC (derives g) s sf ⇒ negr g g' ⇒
 (s=[NTS (startSym g)]) ⇒ ∀sf'. no_rhs g sf sf' ⇒  ~(sf'=[]) ⇒ 
 RTC (derives g') s sf'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES]
THENL[
 `sf'=[NTS (startSym g)]` by 
      (FULL_SIMP_TAC (srw_ss()) [no_rhs,munge0] THEN 
       Cases_on `nullable g [NTS (startSym g)]` THEN 
       FULL_SIMP_TAC (srw_ss()) []) THEN SRW_TAC [] [RTC_RULES],

      FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
      `∃ s1' rhs' s2'.(sf''=(s1'++rhs'++s2')) ∧ no_rhs g s1 s1' ∧ 
      no_rhs g rhs rhs' ∧ no_rhs g s2 s2'` by METIS_TAC [negr_r14]
      THEN Cases_on `rhs'=[]` 
 THENL[
       `no_rhs g [NTS lhs] []` by 
       (SRW_TAC [] [no_rhs,munge0] THEN 
	METIS_TAC [negr_r10,RTC_RULES,negr_r1,res1,no_rhs]) THEN
       `no_rhs g (s1++[NTS lhs]++s2) (s1'++s2')` by METIS_TAC [negr_r12b,APPEND_NIL] THEN
       `~(sf=[])` by SRW_TAC [] [] THEN METIS_TAC [APPEND_NIL],

       `no_rhs g (s1++[NTS lhs]++s2) (s1'++[NTS lhs]++s2')` 
       by METIS_TAC [negr_r5,negr_r12b,no_rhs] THEN
       `~(sf=[]) ∧ ~((s1' ++ [NTS lhs] ++ s2')=[])` by SRW_TAC [] []  THEN 
       `RTC (derives g') [NTS (startSym g)] (s1' ++ [NTS lhs] ++ s2')` 
       by METIS_TAC []  THEN 
       `derives g [NTS lhs] rhs` by METIS_TAC [res1] THEN
       `derives g' [NTS lhs] rhs'` by METIS_TAC [negr_r7] THEN
       `derives g' (s1'++[NTS lhs]++s2') (s1'++rhs'++s2')` 
       by METIS_TAC [derives_same_append_left,derives_same_append_right] THEN
       METIS_TAC [RTC_RULES_RIGHT1]]]);

val thm4_3 = store_thm ("thm4_3",
``negr g g' ⇒ ~([] IN language g) ⇒ (language g = language g')``,
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM]
THENL[
`~nullable g [NTS (startSym g)]` by METIS_TAC [nullable] THEN 
`~(x=[])` by METIS_TAC [negr_r10,eq_snegr] THEN
`no_rhs g x x` by METIS_TAC [negr_r5,no_rhs] THEN
METIS_TAC [eq_snegr,negr_r15],
METIS_TAC [negr_r3,eq_snegr]]);

val _ = export_theory ();