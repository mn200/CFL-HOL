(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory listTheory rich_listTheory;
open pred_setTheory listLemmasTheory;

val _ = new_theory "regexp";


val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

val _ = Hol_datatype `symbol = NTS of 'nts | TS of 'ts`;


val isTmnlSym_def = Define
`(isTmnlSym sym = (∃s.sym = (TS s)))`;

val isNonTmnlSym_def = Define
`isNonTmnlSym sym = (∃s.sym = (NTS s)) ∨ F`;

val tmnlSym_def = Define `tmnlSym (TS tmnl) = tmnl`;
val nonTmnlSym_def = Define `nonTmnlSym (NTS ntmnl) = ntmnl`;

val nts2str = Define `nts2str (NTS s) = s`

val ts2str = Define `ts2str (TS s) = s`

val toTmnlSym = Define `toTmnlSym s = TS s`;

val symToStr_def = Define
`(symToStr (TS s) = s) ∧ (symToStr (NTS s) = s)`;


val sym_r1a = store_thm ("sym_r1a",
``isTmnlSym e ⇒ ¬ isNonTmnlSym e``,
SRW_TAC [] [isTmnlSym_def,isNonTmnlSym_def] THEN
Cases_on `e` THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def] );


val sym_r1b = store_thm ("sym_r1b",
``¬isTmnlSym e = isNonTmnlSym e``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Cases_on `e` THENL[
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def],
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,isTmnlSym_def]],
Cases_on `e` THENL[
FULL_SIMP_TAC (srw_ss())[isTmnlSym_def,isNonTmnlSym_def],
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,isTmnlSym_def]]]);

val sym_r2 = store_thm ("sym_r2",
``isTmnlSym e ⇒ ¬(∃n.e=NTS n)``,
SRW_TAC [] [] THEN
Cases_on `e=NTS n` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);

val sym_r3 = store_thm ("sym_r3",
``∀v.EVERY isTmnlSym v
             ⇒
       ¬(∃n s1 s2.(v=s1++[n]++s2) ∧ isNonTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM]THEN
Cases_on `n` THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EQ_IMP_THM]);


val sym_r3b = store_thm ("sym_r3b",
``∀v.EVERY isNonTmnlSym v
             ⇒
        ¬(∃n s1 s2.(v=s1++[n]++s2) ∧ isTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM]THEN
Cases_on `n` THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EQ_IMP_THM]);


val sym_r4 = store_thm ("sym_r4",
``∀v.EVERY isTmnlSym v ⇒ ¬(∃n. MEM n v ∧ ¬isTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
Cases_on `n` THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,MEM]);


val sym_r4b = store_thm ("sym_r4b",
``∀v.¬EVERY isTmnlSym v ⇒ (∃n. MEM n v ∧ isNonTmnlSym n)``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,EXISTS_MEM] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,MEM,sym_r1b]);


val sym_r5 = store_thm ("sym_r5",
``∀v.¬(∃n s1 s2.(v=s1++[n]++s2) ∧ isNonTmnlSym n)
               ⇒
          EVERY isTmnlSym v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
SRW_TAC [] [] THEN
Cases_on `e` THEN
SRW_TAC [] [isTmnlSym_def, isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
METIS_TAC [isNonTmnlSym_def,isTmnlSym_def]);

val sym_r6 = store_thm ("sym_r6",
``∀v.EVERY isTmnlSym v =
         (¬(∃n s1 s2.(v=s1++[n]++s2) ∧ isNonTmnlSym n))``,
SRW_TAC [] [EQ_IMP_THM] THENL[
METIS_TAC [sym_r3], METIS_TAC [sym_r5]]);

val sym_r7 = store_thm ("sym_r7",
``∀v.¬(EVERY isTmnlSym v)
             ⇒
       ∃n s1 s2.(v=s1++[n]++s2) ∧ isNonTmnlSym n``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,rgr_r9eq,sym_r1b] THEN
MAP_EVERY Q.EXISTS_TAC [`e`,`r1`,`r2`] THEN
SRW_TAC [] []
);


val sym_r7b = store_thm ("sym_r7b",
``∀v.¬(EVERY isNonTmnlSym v)
              ⇒
        ∃n s1 s2.(v=s1++[n]++s2) ∧ isTmnlSym n``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,rgr_r9eq,sym_r1b] THEN
MAP_EVERY Q.EXISTS_TAC [`e`,`r1`,`r2`] THEN
METIS_TAC [sym_r1b]
);



val rightnt = store_thm ("rightnt",
``!s.~EVERY isTmnlSym s ==>
?l1 n l2. (s= l1++[NTS n]++l2) /\ EVERY isTmnlSym l2``,
Induct_on `s` THEN SRW_TAC [] [] THENL[
Cases_on `EVERY isTmnlSym s` THENL[
Cases_on `h` THEN METIS_TAC [isTmnlSym_def, APPEND],
METIS_TAC [APPEND]],
`~ EVERY isTmnlSym s` by SRW_TAC [] [] THEN METIS_TAC [APPEND]])


(* Regular Expressions *)

(* Definition of a regexp *)

val _ = Hol_datatype
`rexp =    EmptyLang
           | Atom of ('ts,'nts) symbol
	   | Union of rexp => rexp
	   | Conc of rexp => rexp
	   | Star of rexp`;


(* Concatenation *)
(* conc :: a list set => a list set => a list set
val conc_def = Define `(conc [] (b::bs) = (b::bs)) ∧ (conc (a::as) (b::bs) = (MAP (STRCAT a) (b::bs)) ++ (conc as (b::bs)))`;
*)

val conc_def = Define
`conc as bs = {s | ∃u v. u ∈ as ∧ v ∈ bs ∧ (s = u ++ v)}`;

(* Union *)
val union_def = Define
`union as bs = {s | s ∈ as ∨ s ∈ bs}`;

(*
Star
(defined inductively)

star :: a list set => a list set
[] <- star A
a <- A and as <- star A => a++as <- star A
*)


val starn_def = Define
`(starn l 0 = {[]})  ∧
(starn l n =
{s | ∃u v. u ∈ l ∧ v ∈ (starn l (n-1)) ∧ (s =  u ++ v)})`;
(* Define A* + prove alternate defn of * *)

val (star_rules, star_ind, star_cases) = Hol_reln
`(star A []) ∧
(∀s. s ∈ A ⇒ star A s) ∧
(∀s1 s2. s1 ∈ A ∧ (star A s2) ⇒ star A (s1 ++ s2))`;

(* Language denoted by a rexp *)
(* lang :: a rexp => a list set *)
(* Includes nonterms as well *)
val lang_def = Define
`(lang EmptyLang = {}) ∧
(lang (Atom tmnl) = {[symToStr tmnl]}) ∧
(lang (Union r s) = lang r UNION lang s) ∧
(lang (Conc r s) = conc (lang r) (lang s)) ∧
(lang (Star r) = star (lang r))`;


val listCompLens = store_thm ("listCompLens",
``∀t t' s2 N rst.(t' ++ s2 = t ++ [NTS N] ++ rst) ⇒
(t=t') ∨ (∃pfx sfx.(t'=t++[NTS N]++pfx) ∧ (rst=pfx++sfx)) ∨ (∃pfx sfx.(t=pfx++sfx) ∧ (t'=pfx))``,
SRW_TAC [] [] THEN
Cases_on `LENGTH  t = LENGTH t'`
THENL[
      METIS_TAC [len1, APPEND, APPEND_ASSOC],

      `(LENGTH t < LENGTH t') ∨ (LENGTH t > LENGTH t')` by FULL_SIMP_TAC (arith_ss) []
      THENL[
	    `∃pfx sfx.(t'=pfx++sfx) ∧ (t=pfx)` by METIS_TAC [len2, APPEND, APPEND_ASSOC] THEN
	    SRW_TAC [] [] THEN
	    Cases_on `pfx` THEN SRW_TAC [] [] THEN
	    Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) []
	    THENL[
		  METIS_TAC [],

		  `h'::t' ++ s2 = [NTS N] ++ rst` by METIS_TAC [listStartSame, APPEND, APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC [APPEND, APPEND_ASSOC]
		  ],


	    `∃pfx sfx.(t=pfx++sfx) ∧ (t'=pfx)` by METIS_TAC [len3, APPEND, APPEND_ASSOC] THEN
	    SRW_TAC [] []
	    ]]);


val symlistnil = store_thm
("symlistnil",
``EVERY isTmnlSym l ∧ EVERY isNonTmnlSym l = (l=[])``,
Cases_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def]);

val symListDiv = store_thm
    ("symListDiv",
     ``(pfx ++ sfx = s1 ++ [NTS lhs] ++ s2) ∧
     EVERY isTmnlSym pfx ∧ EVERY isNonTmnlSym sfx ∧
     EVERY isTmnlSym s1
     ⇒
     (pfx=s1) ∧ (sfx = [NTS lhs]++s2)``,

     SRW_TAC [][] THEN
     IMP_RES_TAC listCompLens THEN
     SRW_TAC [][] THEN
     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
     THENL[
	   `sfx=sfx'++[NTS lhs]++s2` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	   Cases_on `sfx'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	   Cases_on`h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,
						      isNonTmnlSym_def],

	   METIS_TAC [APPEND_ASSOC,APPEND_11,APPEND],

	   `sfx = sfx'++[NTS lhs]++s2` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	   Cases_on `sfx'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	   Cases_on`h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,
						      isNonTmnlSym_def]
	   ]);



val symlistdiv3 = store_thm
("symlistdiv3",
``(s1 ++ [NTS lhs] ++ s2 = x ++ m ++ y)  ∧ (m≠[]) ∧
EVERY isTmnlSym s1 ∧ EVERY isTmnlSym x ∧ EVERY isNonTmnlSym m
⇒
(s1=x) ∧ ([NTS lhs]++s2=m++y)``,

SRW_TAC [][] THEN
`x++(m++y) = s1++[NTS lhs]++s2` by METIS_TAC [APPEND_ASSOC] THEN
IMP_RES_TAC listCompLens THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      `m++y = sfx ++ [NTS lhs] ++ s2` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
      THENL[
	    `m = TS t'::t ++ [NTS lhs]` by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

	    `m = TS t'::t ++ [NTS lhs]++s1'` by METIS_TAC [APPEND_ASSOC,
							   APPEND_11] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

	    `m++s1 = TS t'::t ++ [NTS lhs]` by METIS_TAC [APPEND_ASSOC,
							  APPEND_11] THEN
	    Cases_on `m` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]
	    ],

      METIS_TAC [APPEND_ASSOC,APPEND_11,APPEND],

      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      `m++y = sfx++[NTS lhs]++s2` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `m` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def]
      ]);



val symlistBdwn = store_thm
("symlistBdwn",
``(h ++ sfx ++ sfx' = e0 ++ sfx ++ v' ++ [NTS B] ++ w ++ s2) ∧
EVERY isTmnlSym (h++sfx++e0++v') ⇒
∃s0 s1.(sfx'=s0++[NTS B]++s1) ∧ EVERY isTmnlSym s0 ∧
		   (h++sfx++s0=e0++sfx++v') ∧
		   ([NTS B]++s1 = [NTS B]++w++s2)``,

SRW_TAC [][] THEN
`(h ++ sfx) ++ sfx' = (e0 ++ sfx ++ v') ++ [NTS B] ++ (w ++ s2)`
		   by METIS_TAC [APPEND_ASSOC] THEN
IMP_RES_TAC listCompLens THEN
SRW_TAC [][]
THENL[
      `sfx' = [NTS B] ++ (w ++ s2)`
      by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      METIS_TAC [APPEND_NIL,APPEND,APPEND_ASSOC,EVERY_DEF],

      `EVERY isTmnlSym [NTS B]` by METIS_TAC [EVERY_APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

      METIS_TAC [APPEND_ASSOC,APPEND_11],

      METIS_TAC [APPEND_ASSOC,APPEND_11,EVERY_APPEND]
      ]);




val ldNts = Define
`ldNts dl = FILTER isNonTmnlSym (FLAT dl)`;

val distinctldNts = Define
`distinctldNts dl = rmDupes (ldNts dl)`;


val memldNts = store_thm
("memldNts",
``∀t.MEM (NTS A) (ldNts t) ⇔ ∃e.MEM e t ∧ MEM (NTS A) e``,

SRW_TAC [][ldNts] THEN
FULL_SIMP_TAC (srw_ss()) [FILTER_FLAT,EQ_IMP_THM] THEN
SRW_TAC [][]
THENL[
      `∃e'. MEM e' (MAP (FILTER isNonTmnlSym) t) ∧ MEM (NTS A) e'`
      by METIS_TAC [flat_map_mem] THEN
      FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [MEM_FILTER] THEN
      SRW_TAC [][] THEN
      METIS_TAC [],

      FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
      SRW_TAC [][FILTER_APPEND,isNonTmnlSym_def] THEN
      METIS_TAC [rgr_r9eq,MEM_FLAT]
      ]);


val memdistNtsApp = store_thm
("memdistNtsApp",
 ``∀l1 l2.
 MEM e (distinctldNts l1) ∨ MEM e (distinctldNts l2) ⇔
 MEM e (distinctldNts (l1 ++ l2))``,

Induct_on `l1` THEN SRW_TAC [][] THEN1
SRW_TAC [][distinctldNts,ldNts,rmDupes] THEN

FULL_SIMP_TAC (srw_ss()) [distinctldNts,ldNts,rmDupes] THEN
SRW_TAC [][EQ_IMP_THM,rmDupes] THEN
FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [GSYM rmd_r2] THEN
METIS_TAC []);


val memdistNtsApp' = store_thm
("memdistNtsApp'",
``∀x y.MEM e (distinctldNts [x]) ∨ MEM e (distinctldNts [y]) ⇔
    MEM e (distinctldNts [x ++ y])``,

Induct_on `x` THEN SRW_TAC [][] THEN1
SRW_TAC [][distinctldNts,ldNts,rmDupes] THEN

FULL_SIMP_TAC (srw_ss()) [distinctldNts,ldNts,rmDupes] THEN
SRW_TAC [][EQ_IMP_THM,rmDupes] THEN
(Cases_on `e=h` THEN SRW_TAC [][] THEN
 METIS_TAC [delete_mem_list, rmd_del]));


val ldNtsApp = store_thm
("ldNtsApp",
``∀l1 l2.ldNts (l1++l2) = ldNts l1 ++ ldNts l2``,

Induct_on `l1` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [ldNts,FILTER_APPEND]);

val distElemSubset = Define
`distElemSubset dl dl'  =
   (∀e.MEM e (distinctldNts dl') ⇒ MEM e (distinctldNts dl))`;

val distElemLen = Define
`distElemLen dl dl'  =
(LENGTH (distinctldNts dl') ≤ LENGTH (distinctldNts dl))`;

val distLenAddElem = store_thm
("distLenAddElem",
``∀dl1 l.LENGTH (distinctldNts dl1) ≤ LENGTH (distinctldNts l)
⇒
LENGTH (distinctldNts dl1) ≤ LENGTH (distinctldNts (e::l))``,

SRW_TAC [][distinctldNts] THEN
`ldNts (e::l) = ldNts [e] ++ ldNts l` by METIS_TAC [APPEND,ldNtsApp] THEN
ONCE_ASM_REWRITE_TAC[] THEN
`LENGTH (rmDupes (ldNts l)) ≤ LENGTH (rmDupes (ldNts [e] ++ ldNts l))`
by METIS_TAC [rmdLenLe,APPEND_NIL] THEN
DECIDE_TAC);

val lendistNtsApp' = store_thm
("lendistNtsApp'",
``∀x p s.LENGTH (distinctldNts [x]) ≤ LENGTH (distinctldNts [p++x++s])``,

Induct_on `x` THEN SRW_TAC [][] THEN1
SRW_TAC [][distinctldNts,ldNts,rmDupes] THEN

FULL_SIMP_TAC (srw_ss()) [distinctldNts,ldNts,rmDupes] THEN
SRW_TAC [][EQ_IMP_THM,rmDupes] THEN
SRW_TAC [][rmd_del] THEN
Cases_on `MEM h (rmDupes (FILTER isNonTmnlSym x))` THEN1
 (IMP_RES_TAC delete_mem_len THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`p++[h]`,`s`] MP_TAC) THEN SRW_TAC [][] THEN
  `SUC
  (LENGTH (delete h (rmDupes (FILTER isNonTmnlSym x)))) ≤
  LENGTH (rmDupes (FILTER isNonTmnlSym (p ++ [h]++x ++ s)))` by DECIDE_TAC THEN
  METIS_TAC [APPEND,APPEND_ASSOC])
 THENL[
       IMP_RES_TAC notMem_delete_len THEN
       `LENGTH (FILTER isNonTmnlSym (p ++ h::x ++ s)) >
       LENGTH (rmDupes (FILTER isNonTmnlSym x))` by
       (FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND] THEN
	`LENGTH (FILTER isNonTmnlSym x) ≥
	LENGTH (rmDupes (FILTER isNonTmnlSym x))` by METIS_TAC [rmDupes_len] THEN
	DECIDE_TAC) THEN
       `LENGTH (FILTER isNonTmnlSym (p ++ h::x ++ s)) ≥
       LENGTH (rmDupes (FILTER isNonTmnlSym (p ++ h::x ++ s)))`
       by METIS_TAC [rmDupes_len] THEN
       Cases_on `h` THEN
       FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, FILTER_APPEND] THEN
       Q.ABBREV_TAC `X= (FILTER isNonTmnlSym x)` THEN
       Q.ABBREV_TAC `P = (FILTER isNonTmnlSym p)` THEN
       Q.ABBREV_TAC `SF = (FILTER isNonTmnlSym s)` THEN
       METIS_TAC [notMemRmDLen],


       Q.ABBREV_TAC `X= (FILTER isNonTmnlSym x)` THEN
       Q.ABBREV_TAC `P = (FILTER isNonTmnlSym p)` THEN
       Q.ABBREV_TAC `SF = (FILTER isNonTmnlSym s)` THEN
       Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND,isNonTmnlSym_def] THEN
       UNABBREV_ALL_TAC THEN
       `MEM (TS t) (FILTER isNonTmnlSym x)` by METIS_TAC [rmd_r2] THEN
       FULL_SIMP_TAC (srw_ss()) [MEM_FILTER],

       Q.ABBREV_TAC `X= (FILTER isNonTmnlSym x)` THEN
       Q.ABBREV_TAC `P = (FILTER isNonTmnlSym p)` THEN
       Q.ABBREV_TAC `SF = (FILTER isNonTmnlSym s)` THEN
       Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND,isNonTmnlSym_def] THEN
       METIS_TAC []
       ]);


val distElemSS_trans = store_thm(
  "distElemSS_trans",
  ``distElemSubset dl2 dl1 ∧ distElemSubset dl3 dl2 ⇒ distElemSubset dl3 dl1``,
  SRW_TAC [][distElemSubset]);

val disElemSS_append = store_thm(
  "disElemSS_append",
  ``(distElemSubset q p ⇒ distElemSubset (q ++ q') p) ∧
    (distElemSubset q p ⇒ distElemSubset (q' ++ q) p)``,
  SRW_TAC [][distElemSubset, GSYM memdistNtsApp]);

val disElemSS_refl = store_thm(
  "disElemSS_refl",
  ``distElemSubset p p``,
  SRW_TAC [][distElemSubset]);

val desApp = store_thm
("desApp",
``∀dl1.distElemSubset dl dl1 ⇒ distElemSubset (l1 ++ dl ++ l2) dl1``,
REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL distElemSS_trans) THEN
Q.EXISTS_TAC `dl` THEN SRW_TAC [][disElemSS_append, disElemSS_refl]);


val LENGTH_distinctldNts = store_thm(
  "LENGTH_distinctldNts",
  ``LENGTH (distinctldNts d) = CARD (set (ldNts d))``,
  SRW_TAC [][distinctldNts, rmDupes_lts_card, rmDupes_lts_card_eq]);

(* NOT TRUE: if p++e++s is already in l then its length is unchanged, but
             e may not be in dl1, making its length one bigger. *)
(* val distLenAddElem2 = store_thm
("distLenAddElem2",
 ``∀dl1 l.
     LENGTH (distinctldNts dl1) ≤ LENGTH (distinctldNts l) ∧
     distElemSubset l dl1
   ⇒
     LENGTH (distinctldNts (e::dl1)) ≤ LENGTH (distinctldNts ((p++e++s)::l))``,
 SRW_TAC [][LENGTH_distinctldNts]

*)

val memdist = store_thm
("memdist",
``∀dl.distElemSubset ((pfx++rhs++s2)::l) dl ⇒
 distElemSubset ((pfx++[NTS lhs]++s2)::(pfx++rhs++s2)::l) ((NTS lhs::s2)::dl)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1

(FULL_SIMP_TAC (srw_ss()) [distinctldNts, distElemSubset, ldNts, rmDupes,
			  isNonTmnlSym_def] THEN
SRW_TAC [][FILTER_APPEND] THEN
METIS_TAC [isNonTmnlSym_def, rmd_r2, MEM, MEM_APPEND, memdel]) THEN

FULL_SIMP_TAC (srw_ss()) [distElemSubset] THEN
SRW_TAC [][] THEN
METIS_TAC [memdistNtsApp, APPEND, APPEND_ASSOC]);



val memdist' = store_thm
("memdist'",
``∀dl.distElemSubset ((p++pfx++rhs++s2++s2')::l) dl ⇒
 distElemSubset ((p++pfx++[NTS lhs]++s2++s2')::(p++pfx++rhs++s2++s2')::l)
 ((pfx++[NTS lhs]++s2)::dl)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1

(FULL_SIMP_TAC (srw_ss()) [distinctldNts, distElemSubset, ldNts, rmDupes,
			  isNonTmnlSym_def] THEN
SRW_TAC [][FILTER_APPEND] THEN
METIS_TAC [isNonTmnlSym_def, rmd_r2, MEM, MEM_APPEND, memdel]) THEN

FULL_SIMP_TAC (srw_ss()) [distElemSubset] THEN
SRW_TAC [][] THEN
METIS_TAC [memdistNtsApp, APPEND, APPEND_ASSOC]);



(* false again for the same reason (this goal is ridiculously specific as well)
val lendist' = store_thm
("lendist'",
``∀dl.  distElemLen ((p++pfx++rhs++s2++s2')::l) dl ⇒
        distElemLen ((p++pfx++[NTS lhs]++s2++s2')::(p++pfx++rhs++s2++s2')::l)
                    ((pfx++[NTS lhs]++s2)::dl)``,
SRW_TAC [][distElemLen, LENGTH_distinctldNts]

Induct_on `dl` THEN SRW_TAC [][] THEN

FULL_SIMP_TAC (srw_ss()) [distElemLen, distinctldNts, ldNts, rmDupes,
			  isNonTmnlSym_def, FILTER_APPEND] THEN
MAGIC);
*)


(* false  if dl1 = l, and p ++ [e] ++ s is in l already
val distLenAddElemNew = store_thm
("distLenAddElemNew",
``∀dl1 l.
    LENGTH (distinctldNts dl1) ≤ LENGTH (distinctldNts l) ∧
    distElemSubset l dl1
  ⇒
    LENGTH (distinctldNts dl1) ≤ LENGTH (distinctldNts ((p++[e]++s)::l)) - 1``,
SRW_TAC [][LENGTH_distinctldNts]
MAGIC);
*)

val distesubaddlist = store_thm
("distesubaddlist",
``distElemSubset dl l ⇒ distElemSubset (p++dl++s) l``,
SRW_TAC [][distElemSubset] THEN
FULL_SIMP_TAC (srw_ss()) [distinctldNts,ldNts] THEN
Q_TAC SUFF_TAC `MEM e (FILTER isNonTmnlSym (FLAT (p ++ dl ++ s)))` THEN1
METIS_TAC [rmd_r2] THEN
`MEM e (FILTER isNonTmnlSym (FLAT l))` by METIS_TAC [rmd_r2] THEN
SRW_TAC [][FLAT_APPEND,FILTER_APPEND] THEN
METIS_TAC [rmd_r2]);

val distesub1 = store_thm
("distesub1",
``∀h t dl1.(∀e.MEM e dl1 ⇒ ∃e1.(HD dl1 ++ e1 = h) ∧
	    ((e ++ e1 = h) ∨ MEM (e ++ e1) t))
    ⇒
    distElemSubset (h::t) dl1``,

Cases_on `dl1` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [distElemSubset,distinctldNts,ldNts,rmDupes] THEN
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `MEM e (FILTER isNonTmnlSym (h' ++ FLAT t'))` THEN1
METIS_TAC [rmd_r2] THEN
`MEM e (FILTER isNonTmnlSym (h ++ FLAT t))` by METIS_TAC [rmd_r2] THEN
FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND,MEM_FILTER] THEN
`∃e1.(h ++ e1 = h') ∧ ((h ++ e1 = h') ∨ MEM (h ++ e1) t')` by METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_FLAT] THEN
METIS_TAC [rgr_r9eq,rmd_r2,MEM,MEM_APPEND,MEM_FLAT,APPEND_ASSOC]);

val distesub2 = store_thm
("distesub2",
 ``∀h t dl2.
 (∀e.MEM e dl2 ⇒ ∃e0.EVERY isTmnlSym e0 ∧ ((e0 ++ e = h) ∨ MEM (e0 ++ e) t))
 ⇒
 distElemSubset (h::t) dl2``,

Cases_on `dl2` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [distElemSubset,distinctldNts,ldNts,rmDupes] THEN
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `MEM e (FILTER isNonTmnlSym (h' ++ FLAT t'))` THEN1
METIS_TAC [rmd_r2] THEN
 `MEM e (FILTER isNonTmnlSym (h ++ FLAT t))` by METIS_TAC [rmd_r2] THEN
FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND,MEM_FILTER] THEN
 `∃e0.EVERY isTmnlSym e0 ∧((e0 ++ h = h') ∨ MEM (e0 ++ h) t')` by METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_FLAT] THEN
METIS_TAC [rgr_r9eq,rmd_r2,MEM,MEM_APPEND,MEM_FLAT,APPEND_ASSOC]);


val _ = export_theory ();

