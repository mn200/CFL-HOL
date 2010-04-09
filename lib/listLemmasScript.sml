(* A theory about lists *)
open HolKernel boolLib bossLib Parse
open stringTheory containerTheory

open pred_setTheory listTheory arithmeticTheory Defn optionTheory
pred_setSimps rich_listTheory

open containerLemmasTheory

val _ = new_theory "listLemmas";

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

(* 14/05/07 AB *)
val _ = Globals.linewidth := 60
val _ = diminish_srw_ss ["list EQ"];
val _ = overload_on ("IN", ``MEM``);


val list_l1 = store_thm ("list_l1",
``!r.(r=[]) = NULL r``,
Induct_on `r` THEN SRW_TAC [] [])


val filter_l1 = store_thm ("filter_l1",
``!p l.LENGTH (FILTER p l) > 0 ==> (?e.MEM e l /\ p e)``,
Induct_on `l` THEN SRW_TAC [] [] THEN METIS_TAC []
)

val len_not_0 = store_thm ("len_not_0",
``!l.~(LENGTH l = 0) = ?h t.(l=h::t)``,
Induct_on `l` THEN SRW_TAC [] [])

val filter_l2 = store_thm ("filter_l2",
``!f l.(LENGTH (FILTER f l) = 0) = ~(?e.MEM e l /\ f e)``,
SRW_TAC [] [EQ_IMP_THM] THEN
Induct_on `l` THEN SRW_TAC [] [] THEN METIS_TAC []
)

val lres = store_thm ("lres",
``(l1 ++ [x] ++ l2 = [y]) ==> ((l1=[]) /\ (l2=[]) /\ (x=y))``,
Cases_on `l1` THEN SRW_TAC [] []
);

val lresb = store_thm ("lresb",
``((l1=[]) /\ (l2=[]) /\ (x=y)) ==> (l1 ++ [x] ++ l2 = [y])``,
SRW_TAC [] []
);

val lreseq = store_thm ("lreseq",
``(l1 ++ [x] ++ l2 = [y]) = ((l1=[]) /\ (l2=[]) /\ (x=y))``,
METIS_TAC [EQ_IMP_THM,lres,lresb]
);


val rgr_r9 = store_thm ("rgr_r9",
``!r.MEM sym r ==> ?r1 r2.r=r1++[sym]++r2``,
Induct_on `r` THENL
[
SRW_TAC [] [],
SRW_TAC [] [] THEN
SRW_TAC [] [] THENL
[
MAP_EVERY Q.EXISTS_TAC [`[]`,`r`] THEN SRW_TAC [] [],
RES_TAC THEN
MAP_EVERY Q.EXISTS_TAC [`h::r1`,`r2`] THEN SRW_TAC [] []
]]
);


 val rgr_r9b = store_thm ("rgr_r9b",
``!r.(?r1 r2.(r=r1++[sym]++r2)) ==> MEM sym r``,
SRW_TAC [] [rgr_r9] THEN SRW_TAC [] [rgr_r9]
);


val rgr_r9eq = store_thm ("rgr_r9eq",
``!r.MEM sym r = (?r1 r2.(r=r1++[sym]++r2))``,
METIS_TAC [rgr_r9,rgr_r9b,EQ_IMP_THM,EQ_SYM]
);

val list_r1 = store_thm ("list_r1",
``!v v' x.(v=v'++[x]) ==> MEM x v``,
SRW_TAC [] []);

val list_r2 = store_thm ("list_r2",
``!s1 s2 rhs x.(s1 ++ rhs ++ s2 = [x]) ==> ~(rhs=[]) ==> (s1=[]) /\ (s2=[])``,
SRW_TAC [][APPEND_EQ_SING]);

val list_r6 = store_thm ("list_r6",
``!s1 s2 s1' s2' x.(s1' ++ [x] ++ s2' = s1 ++ s2) ==> ?l1 l2.((s1=s1'++[x]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/ ((s2=l2++[x]++s2') /\ (s1=l1) /\ (s1'=l1++l2))``,
Induct_on `s1'` THENL[
  SRW_TAC [] [EXISTS_OR_THM] THEN
  Cases_on `s1` THEN SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [],
  SRW_TAC [] [] THEN Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN FULL_SIMP_TAC (srw_ss()) [EXISTS_OR_THM]
])

val list_lem1 = store_thm ("list_lem1",
``!l.(LENGTH l = 1) = ?e.l=[e]``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL],
FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
])


val list_lem2 = store_thm ("list_lem2",
``!l.(LENGTH l = 2) = ?e1 e2.l=[e1;e2]``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,list_lem1],
FULL_SIMP_TAC (srw_ss()) [LENGTH]
])

val list_lem3 = store_thm ("list_lem3",
``!l.(LENGTH l >= 3) = ?e1 e2 e3 r.(l=[e1;e2;e3]++r)``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN
`LENGTH l >= 2` by DECIDE_TAC THEN
`(LENGTH l = 2) \/ (LENGTH l > 2)` by METIS_TAC [GREATER_OR_EQ] THENL[
METIS_TAC [list_lem2],
`LENGTH l >= 3` by DECIDE_TAC THEN METIS_TAC []],
FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC
])

val list_lem4 = store_thm ("list_lem4",
``!l.(LENGTH l >= 2) = ?e1 e2 r.(l=[e1;e2]++r)``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN
`LENGTH l >= 1` by DECIDE_TAC THEN
`(LENGTH l = 1) \/ (LENGTH l > 1)` by METIS_TAC [GREATER_OR_EQ] THENL[
METIS_TAC [list_lem1],
`LENGTH l >= 2` by DECIDE_TAC THEN METIS_TAC []],
FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC
])

val l_lemma1 = store_thm("l_lemma1",
``!r.(1 <= LENGTH r) ==> ?h' r'.(r=(h'::r'))``,
Induct_on `r` THEN
SRW_TAC [] []
)

val sl_1 = store_thm ("sl",
``!p s x.LENGTH (p++[x]++s) >= 3 ==> (~NULL s \/ ~NULL p)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN Cases_on `s` THENL[
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [NULL_DEF],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL]
])

val sl_l2 = store_thm ("sl_l2",
``!p s x.(LENGTH (p ++ [NTS t1] ++ s) >= 2) ==> (~NULL s \/ ~NULL p)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN Cases_on `s` THENL[
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [NULL_DEF],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL]
])

val sl_l3 = store_thm ("sl_l3",
``!p s.(LENGTH p + LENGTH s >= 1) ==> (~NULL s \/ ~NULL p)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL]
)

val len0 = store_thm("len0",
``!s.NULL s = (LENGTH s = 0)``,
Cases_on `s` THEN
SRW_TAC [] [])

val notLen1 = store_thm("notLen1",
 ``!p s.(~NULL p \/ ~NULL s) ==> !x.~(LENGTH (p++[x]++s)<=1)``,
SRW_TAC [] [] THENL[
`~(p=[])` by METIS_TAC [list_l1] THEN
`~(LENGTH p = 0)` by METIS_TAC [LENGTH_NIL] THEN
`1 <= LENGTH p` by DECIDE_TAC THEN
`?h' r'.(p=(h'::r'))` by METIS_TAC [l_lemma1] THEN
`LENGTH (h'::r') = LENGTH ([h']++r')` by METIS_TAC [APPEND] THEN SRW_TAC [] [] THEN DECIDE_TAC,
`~(s=[])` by METIS_TAC [list_l1] THEN
`~(LENGTH s = 0)` by METIS_TAC [LENGTH_NIL] THEN
`1 <= LENGTH s` by DECIDE_TAC THEN
`?h' r'.(s=(h'::r'))` by METIS_TAC [l_lemma1] THEN
`LENGTH (h'::r') = LENGTH ([h']++r')` by METIS_TAC [APPEND] THEN SRW_TAC [] [] THEN DECIDE_TAC])

val listNotNull = store_thm("listNotNull",
``!p.~NULL p = ?h t.(p=h::t)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN
SRW_TAC [] [])

val sl_l4 = store_thm("sl_l4",
``!e t1 t2 p s.~([e] = p++[NTS t1;NTS t2]++s)``,
SRW_TAC [] [] THEN Cases_on `p` THEN SRW_TAC [] []
)

val sl_l5 = store_thm("sl_l5",
``!e1 e2 t1 t2 p s.([e1; e2] = p ++ [NTS t1; NTS t2] ++ s) ==> (NULL p /\ NULL s)``,
SRW_TAC [] [] THENL[
Cases_on `p` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [] THEN Cases_on `t` THEN FULL_SIMP_TAC list_ss [],
Cases_on `s` THEN SRW_TAC [] [] THEN
Cases_on `p` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [] THEN Cases_on `t'` THEN FULL_SIMP_TAC list_ss []]
)


val finiteLists = store_thm("finiteLists",
``!l.FINITE (LIST_TO_SET l)``,
Induct_on `l` THEN
 SRW_TAC [] [LIST_TO_SET_THM]
)

val delete = Define `(delete x [] = []) /\
(delete x (l::ls) = if (x=l) then delete x ls else l::delete x ls)`

val diff = Define `(diff l1 [] = l1) /\
(diff [] l2 = []) /\
(diff l1 (l::ls) = if (MEM l l1) then diff (delete l l1) ls else diff l1 ls)`

val delete_not_mem1 = store_thm ("delete_not_mem1",
``!e l.~(MEM e l) ==> ((delete e l) = l)``,
Induct_on `l` THEN SRW_TAC [] [delete])

val delete_append = store_thm ("delete_append",
``!e l1 l2. delete e (l1++l2) = delete e l1 ++ delete e l2``,
Induct_on `l1` THEN SRW_TAC [] [delete])

val not_mem_delete = store_thm ("not_mem_delete",
``!e l.~(MEM e (delete e l))``,
Induct_on `l` THEN SRW_TAC [] [delete])

val delete_not_mem2 = store_thm("delete_not_mem2",
``!e l.(delete e l = l) ==> ~(MEM e l)``,
METIS_TAC [not_mem_delete])


val delete_not_mem = store_thm ("delete_not_mem",
``!e l.(delete e l = l) = ~(MEM e l)``,
METIS_TAC [delete_not_mem1, delete_not_mem2])

val delete_mem_len = store_thm ("delete_mem_len",
``!e l.(MEM e l) ==> (LENGTH (delete e l) < LENGTH l)``,
Induct_on `l` THEN SRW_TAC [] [delete] THEN
Cases_on `MEM e l` THENL[
RES_TAC THEN FULL_SIMP_TAC (arith_ss) [],
`(delete e l = l)` by METIS_TAC [delete_not_mem] THEN
`LENGTH (delete e l) = LENGTH l` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) []])

val delete_nil = store_thm ("delete_nil",
``!e l.(delete e l = []) = ((l=[]) \/ (!el.MEM el l ==> (el=e)))``,
Induct_on `l` THEN SRW_TAC [] [delete, EQ_IMP_THM] THEN
METIS_TAC [MEM])

val delete_mem_list = store_thm("delete_mem_list",
``!e h l.~(h=e) ==> (MEM e l = MEM e (delete h l))``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM, delete] THEN
FULL_SIMP_TAC (srw_ss()) [delete_append, MEM_APPEND, rgr_r9eq, delete, MEM] THEN
METIS_TAC [])

val delete_twice = store_thm("delete_twice",
``!h l.delete h l = delete h (delete h l)``,
Induct_on `l` THEN SRW_TAC [] [delete] THEN
METIS_TAC [])

val delete_diff_elem = store_thm ("delete_diff_elem",
``!h h' l.(delete h (delete h' l)) = (delete h' (delete h l))``,
Induct_on `l` THEN SRW_TAC [] [delete] THEN
METIS_TAC [])


val rmDupes_defn = Hol_defn "rmDupes_defn"
`(rmDupes [] = []) /\
(rmDupes (h::t) = h::rmDupes (delete h t))`

val (rmDupes, rmDupes_ind) = tprove(rmDupes_defn,
WF_REL_TAC `measure (\l.LENGTH l)` THEN
SRW_TAC [] [] THEN
Cases_on `MEM h t` THENL[
`LENGTH (delete h t) < LENGTH t` by METIS_TAC [delete_mem_len] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [],
`LENGTH (delete h t) = LENGTH t` by METIS_TAC [delete_not_mem] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []])


val _ = save_thm ("rmDupes", rmDupes)
val _ = save_thm ("rmDupes_ind", rmDupes_ind)



val rmd_r2_1 = store_thm ("rmd_r2_1",
``!l.MEM e l ==> MEM e (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
Cases_on `e=h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [delete_mem_list])

val rmd_r2_2 = store_thm ("rmd_r2_2",
``!l.MEM e (rmDupes l) ==> MEM e l``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
Cases_on `e=h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [delete_mem_list])

val rmd_r2 = store_thm ("rmd_r2",
``!e l.MEM e l = MEM e (rmDupes l)``,
METIS_TAC [rmd_r2_1, rmd_r2_2]
)

val rmDupes_not_nil = store_thm ("rmDupes_not_nil",
``!x xs.~(rmDupes (x::xs) = [])``,
FULL_SIMP_TAC (srw_ss()) [rmDupes])


val rmd_mem_list1 = store_thm ("rmd_mem_list1",
``!l.MEM e l ==> MEM e (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rmDupes],
Cases_on `h=e` THEN FULL_SIMP_TAC (srw_ss()) [rmDupes] THEN
METIS_TAC [delete_mem_list]])


val rmd_mem_list2 = store_thm ("rmd_mem_list2",
``!l.MEM e (rmDupes l) ==> MEM e l``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
METIS_TAC [delete_mem_list])

val rmd_mem_list = store_thm ("rmd_mem_list",
``!l.MEM e (rmDupes l) = MEM e l``,
METIS_TAC [rmd_mem_list1, rmd_mem_list2])


val rmDupes_len = store_thm ("rmDupes_len",
``!l.LENGTH l >= LENGTH (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
Cases_on `MEM h t` THENL[
`LENGTH (delete h t) < LENGTH t` by METIS_TAC [delete_mem_len] THEN
FULL_SIMP_TAC (arith_ss) [],
`LENGTH (delete h t) = LENGTH t` by METIS_TAC [delete_not_mem] THEN
FULL_SIMP_TAC (arith_ss) []])


val rmd_del = store_thm ("rmd_del",
``!l.rmDupes (delete h l) = delete h (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [delete,rmDupes] THEN
METIS_TAC [delete_twice, delete_diff_elem])


val rmda_del_rmda = store_thm("rmda_del_rmda",
``!l.rmDupes (delete h l) = (rmDupes (delete h (rmDupes (delete h l))))``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, EXTENSION, delete]
THENL[
METIS_TAC [delete_twice],
`delete h' (delete h t) = delete h (delete h' t)` by METIS_TAC [delete_diff_elem] THEN
METIS_TAC [delete_twice, delete_diff_elem,rmd_del]])


val rmDupes_twice = store_thm ("rmDupes_twice",
``!l.(rmDupes (rmDupes l)) = (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
METIS_TAC [rmda_del_rmda])

val delete_lts = store_thm("delete_lts",
``!h l.LIST_TO_SET (delete h l) = (LIST_TO_SET l) DELETE h``,
Induct_on `l` THEN SRW_TAC [] [delete] THEN
SRW_TAC [] [EXTENSION] THEN METIS_TAC [])


val delete_lts = store_thm ("delete_lts",
``!h l.(MEM h l) ==> (LIST_TO_SET l = h INSERT LIST_TO_SET (delete h l))``,
Induct_on `l` THEN SRW_TAC [] [delete] THENL[
Cases_on `MEM h l` THENL[
METIS_TAC [INSERT_INSERT],
`~MEM h (delete h l)` by METIS_TAC [delete_not_mem] THEN
SRW_TAC [] [delete_lts] THEN
METIS_TAC [DELETE_NON_ELEMENT, mem_in]],
METIS_TAC [DELETE_NON_ELEMENT, mem_in, delete_not_mem, INSERT_INSERT, delete_lts, INSERT_COMM]])


val delete_lts_card = store_thm ("delete_lts_card",
``!h l.(MEM h l) ==> (CARD (LIST_TO_SET l) > (CARD (LIST_TO_SET (delete h l))))``,
SRW_TAC [] [] THEN
`(LIST_TO_SET l = h INSERT LIST_TO_SET (delete h l))` by METIS_TAC [delete_lts] THEN
`~(MEM h (delete h l))` by METIS_TAC [not_mem_delete] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
DECIDE_TAC)




val rmDupes_lts = store_thm ("rmDupes_lts",
``!l.LIST_TO_SET l = LIST_TO_SET (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
Cases_on `MEM h t` THEN
METIS_TAC [delete_lts, INSERT_INSERT, delete_not_mem])

val rmDupes_lts_card = store_thm ("rmDupes_lts_card",
``!l.LENGTH (rmDupes l) = CARD (LIST_TO_SET (rmDupes l))``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
METIS_TAC [rmd_mem_list,not_mem_delete])

val rmDupes_lts_card_eq = store_thm ("rmDupes_lts_card_eq",
``!l. CARD (set (rmDupes l)) = CARD (set l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THENL[
  METIS_TAC [rmd_mem_list,not_mem_delete],
  METIS_TAC [rmd_mem_list,not_mem_delete],
  `set t = h INSERT set (delete h t)` by METIS_TAC [delete_lts] THEN
  FULL_SIMP_TAC (srw_ss()) [not_mem_delete],
  METIS_TAC [rmd_mem_list,not_mem_delete, delete_not_mem]
])


val mem_subset_len = store_thm ("mem_subset_len",
``!l1 l2.(!e.MEM e (rmDupes l1) ==> MEM e l2) ==> (LENGTH l2 >= LENGTH (rmDupes l1))``,
SRW_TAC [] [] THEN
`(LIST_TO_SET (rmDupes l1)) SUBSET  (LIST_TO_SET l2)` by METIS_TAC [SUBSET_DEF, mem_in] THEN
`CARD (LIST_TO_SET (rmDupes l1)) <= CARD (LIST_TO_SET l2)` by METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET] THEN
`CARD (LIST_TO_SET l2) >= CARD  (LIST_TO_SET (rmDupes l1))` by DECIDE_TAC THEN
`LENGTH l2 >= CARD (LIST_TO_SET l2)` by METIS_TAC [len_card] THEN
`LENGTH  (rmDupes l1) >= CARD (LIST_TO_SET (rmDupes l1))` by METIS_TAC [len_card] THEN
`LENGTH l2 >= LENGTH (rmDupes l2)` by METIS_TAC [rmDupes_len] THEN
`LENGTH l1 >= LENGTH (rmDupes l1)` by METIS_TAC [rmDupes_len] THEN
`CARD (LIST_TO_SET l1) = CARD (LIST_TO_SET (rmDupes l1))` by METIS_TAC [rmDupes_lts_card_eq] THEN
`CARD (LIST_TO_SET l2) = CARD (LIST_TO_SET (rmDupes l2))` by METIS_TAC [rmDupes_lts_card_eq] THEN
`LENGTH l2 >= CARD (LIST_TO_SET (rmDupes l1))` by FULL_SIMP_TAC (arith_ss) [] THEN
`LENGTH l2 >= CARD (LIST_TO_SET l1)` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [rmDupes_lts_card_eq, rmDupes_lts_card])

val list_set_len = store_thm ("list_set_len",
``!l1 l2.(LENGTH (rmDupes l1) >= LENGTH l2) ==> (CARD (LIST_TO_SET l1) >= CARD (LIST_TO_SET l2))``,
SRW_TAC [] [] THEN
`LENGTH l2 >= CARD (LIST_TO_SET l2)` by METIS_TAC [len_card] THEN
`CARD (LIST_TO_SET (rmDupes l1)) = CARD (LIST_TO_SET l1)` by METIS_TAC [rmDupes_lts_card_eq] THEN
`CARD (LIST_TO_SET (rmDupes l1)) >= LENGTH l2` by METIS_TAC [rmDupes_lts_card] THEN
`CARD (LIST_TO_SET l1) >= LENGTH l2` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) [])

val set_neq_len = store_thm ("set_neq_len",
``!s1.FINITE s1 ==> ~(s1=s2) ==>  (s2 SUBSET s1) ==>
(CARD s1>=CARD s2) ==> (CARD s1>CARD s2)``,
SRW_TAC [] [] THEN
`s2 PSUBSET s1` by METIS_TAC [PSUBSET_DEF] THEN
`CARD s2 < CARD s1` by METIS_TAC [CARD_PSUBSET] THEN
DECIDE_TAC)


val breakAtElem = Define `(breakAtElem e [] = [])
/\ (breakAtElem e (l::ls) = if (e=l) then ls else breakAtElem e ls)`

val push = Define `push l e = e::l`

val push_not_nil = store_thm ("push_not_nil",
``!e l.~(push l e = [])``,
METIS_TAC [push, NOT_CONS_NIL])


val pop = Define `
(pop [] _ = []) /\
(pop (h::t) num = if (num = 0) then (h::t) else pop t (num-1))`

val listNotEmpty = store_thm ("listNotEmpty",
``!l.(?e.MEM e l) = ~(l=[])``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
`?h t.l=h::t` by METIS_TAC [list_l1,CONS] THEN METIS_TAC [APPEND])



val rev_nil = store_thm ("rev_nil",
``!l.(REVERSE l = []) = (l=[])`` ,
Induct_on `l` THEN SRW_TAC [] [])

val list_exists_mem = store_thm ("list_exists_mem",
``!l.~(l=[]) ==> ?e.MEM e l``,
Cases_on `l` THEN SRW_TAC [] [] THEN METIS_TAC [])

val FLAT_APPEND_DISTRIB = store_thm ("FLAT_APPEND_DISTRIB",
``!x y.FLAT (x++y) = FLAT x ++ FLAT y``,
Induct_on `x` THEN SRW_TAC [] [FLAT,APPEND]
)

val flat_map_mem = store_thm ("flat_map_mem",
``!e l.MEM e (FLAT (MAP f l)) ==> (?e'.MEM e' (MAP f l) /\ (MEM e e'))``,
SRW_TAC [] [] THEN
Induct_on `l` THEN
SRW_TAC [] [] THEN
METIS_TAC [])

val popl = store_thm ("popl",
``!l n.(x = pop l n) ==> (?pfx sfx.(l=pfx++sfx) /\ (sfx = x))``,
Induct_on `l` THEN SRW_TAC [] [pop] THEN
METIS_TAC [APPEND] THEN
`?pfx sfx. (l = pfx ++ sfx) /\ (sfx = pop l (n - 1))` by METIS_TAC [] THEN
METIS_TAC [APPEND, APPEND_ASSOC])


val listappnil = store_thm ("listappnil",
``!x.(x = pfx ++ x ) ==> (pfx=[])``,
SRW_TAC [][] THEN
METIS_TAC [APPEND_EQ_SELF]);

val append_eq_sing = store_thm(
  "append_eq_sing",
  ``(p ++ q = [e]) <=> (p = [e]) /\ (q = []) \/ (p = []) /\ (q = [e])``,
  Cases_on `p` THEN SRW_TAC [][CONJ_ASSOC]);

val rev_sing = save_thm ("rev_sing", listTheory.REVERSE_EQ_SING)

val take1_defn = Hol_defn "take1_defn" `(take1 0 [] = []) /\
    (take1 n (x::xs) = (if n=0 then [] else x::take1 (n - 1) xs))`

val (take1, take1_ind) = tprove (take1_defn,
WF_REL_TAC (`measure (\(n,l).LENGTH l)`) THEN
SRW_TAC [] [])

val _ = save_thm ("take1", take1)
val _ = save_thm ("take1_ind", take1_ind)

(*val take1 = Define `(take1 0 [] = []) /\
    (take1 (SUC n) (x::xs) = x::take1 (n - 1) xs)`
*)

(*val take1 = Define `(take1 0 l = []) /\
(take1 n (x::xs) = x::take1 (n-1) xs)`
*)
val take =  Define
`(take n l = if (LENGTH l >= n) then SOME (take1 n l)
			       else NONE)`


val take_len = store_thm ("take_len",
``!n l.~(take n l = NONE) ==> (LENGTH l >=n)``,
SRW_TAC [] [] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [take] THEN
Cases_on `LENGTH l >= SUC n'` THEN FULL_SIMP_TAC (srw_ss()) [take]
)

val take10 = store_thm ("take10",
``!l.take1 0 l = []``,
Induct_on `l` THEN SRW_TAC [] [take1])
val _ = export_rewrites ["take10"]


val take0 = store_thm ("take0",
``take 0 l = SOME []``,
Cases_on `l` THEN SRW_TAC [] [take, take10])
val _ = export_rewrites ["take0"]


val rev_len = store_thm ("rev_len",
``!l.(LENGTH l) = LENGTH (REVERSE l)``,
Induct_on `l` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF, LENGTH, ADD1])



val takeCoMap = store_thm ("takeCoMap",
``!f g l.(take n (MAP (f o g) l) = SOME x) ==>
?x'.(take n (MAP g l) = SOME x')``,
SRW_TAC [] [] THEN
`(LENGTH (MAP (f o g) l)) >= n` by METIS_TAC [take_len, NOT_SOME_NONE] THEN
`(LENGTH (MAP (f o g) l)) = LENGTH l` by METIS_TAC [LENGTH_MAP] THEN
`(LENGTH (MAP g l)) = LENGTH l` by METIS_TAC [LENGTH_MAP] THEN
Cases_on `n` THEN
FULL_SIMP_TAC (srw_ss()) [take]
)

val take1Map = store_thm ("take1Map",
``!f l n.((LENGTH l) >= n) ==> ((take1 n (MAP f l)) = (MAP f (take1 n l)))``,
Induct_on `l` THEN Cases_on `n` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (arith_ss) [ADD1, LENGTH, take1, MAP])

val revTakeMap = store_thm ("revTakeMap",
``!n f l.((take n (MAP f l)) = SOME x) ==>
((REVERSE (THE (take n (MAP f l)))) = (REVERSE (MAP f (THE (take n l)))))``,
Induct_on `n` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [take] THEN
Cases_on `(LENGTH l) >=SUC n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [take, take10] THEN
METIS_TAC [take1Map])

val popnthm = store_thm ("popnthm",
``!pfx rst n.(LENGTH pfx = n) ==> (pop (pfx++rst) n = rst)``,
Induct_on `pfx` THEN SRW_TAC [] [] THENL[
Cases_on `rst` THEN SRW_TAC [] [pop],
SRW_TAC [] [pop]]
)

val take0out = store_thm ("take0out",
``!l.(take 0 l = SOME y) ==> (y=[])``,
Induct_on `l` THEN
METIS_TAC [take, take10, take0, SOME_11])


val takenthm = store_thm ("takenthm",
``∀pfx rst n.(LENGTH pfx = n) ⇒ (take n (pfx++rst) = SOME pfx)``,
SIMP_TAC (srw_ss()) [take] THEN
Induct_on `pfx` THEN SRW_TAC [ARITH_ss][take1]);

val pop0 = store_thm ("pop0",
``!l.(pop l 0) = l``,
Induct_on `l` THEN SRW_TAC [] [pop])


val take_map = store_thm ("take_map",
``!stl.((take (LENGTH r) stl) = SOME x)
==> ((MAP SND (THE (take (LENGTH r) stl)) = (THE (take (LENGTH r) (MAP SND stl)))))``,
Cases_on `LENGTH r` THEN SRW_TAC [] [take] THEN
METIS_TAC [take1Map, take10, take, take1, LENGTH_NIL,MAP]
)


val take_valid = store_thm ("take_valid",
``!l.((LENGTH l) >= n) ==> ?x.((take n l) = SOME x)``,
Cases_on `n` THEN SRW_TAC [] [take]
)


val valid_take_map = store_thm ("valid_take_map",
``!n l.(take n l = SOME x) ==> ?x'.(take n (MAP f l) = SOME x')``,
Cases_on `n` THEN SRW_TAC [] [take]
)

val map_rev = store_thm ("map_rev", ``!l.(MAP f (REVERSE l)) = REVERSE (MAP f l)``,
Induct_on `l` THEN SRW_TAC [] [REVERSE_DEF, MAP])

val map_pop = store_thm ("map_pop",
``!l.(pop (MAP f l) n) = MAP f (pop l n)``,
Induct_on `n` THEN Induct_on `l` THEN SRW_TAC [] [pop]
)


val take_pop = store_thm ("take_pop",
``!l l' n.(take n l = SOME l') ==> (l=l'++ pop l n)``,
Induct_on `l` THEN SRW_TAC [] [] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [take] THEN
Cases_on `SUC (LENGTH l) >= SUC n'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [take1] THEN
SRW_TAC [] [pop] THEN
`LENGTH l >= n'` by FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [SOME_11])



val take_mem = store_thm ("take_mem",
``!n l.(take n l = SOME x) ==> (!e.MEM e x ==> MEM e l)``,
Induct_on `n` THEN SRW_TAC [] [] THENL[
METIS_TAC [take0, SOME_11, take1, take0out, MEM],

`~(SUC n = 0)` by FULL_SIMP_TAC (arith_ss) [] THEN
`?sfx.(l=x++sfx) /\ (sfx=pop l (SUC n))` by METIS_TAC [take_pop] THEN
SRW_TAC [] [] THEN
METIS_TAC [rgr_r9eq, MEM_APPEND]]
)


val listeq = store_thm ("listeq",
``!l1 l2 e l1' l2' e'.(l1++[e]++l2 = l1'++[e']++l2') ==>
~P(e) /\ ~P(e') /\ EVERY P l2 /\ EVERY P l2' ==>
(l1=l1') /\ (e=e') /\ (l2=l2')``,
Induct_on `l1` THENL[
SIMP_TAC (srw_ss()) []  THEN
Cases_on `l1'` THEN SRW_TAC [] [] THEN
METIS_TAC [],
Cases_on `l1'` THEN SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []])

val delete_prop = store_thm ("delete_prop",
``!P l.EVERY P l ==> EVERY P (delete h l)``,
Induct_on `l` THEN SRW_TAC [] [delete] THEN
METIS_TAC [])

val rmDupes_prop = store_thm ("rmDupes_prop",
``! l.EVERY P l ==> EVERY P (rmDupes l)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
METIS_TAC [delete_prop])


val alld_delete = store_thm ("alld_delete",
``!l.ALL_DISTINCT l ==> !h.ALL_DISTINCT (delete h l)``,
Induct_on `l` THEN SRW_TAC [] [delete] THEN
Cases_on `h'=h` THEN SRW_TAC [] [] THEN
METIS_TAC [delete_mem_list])

val alld_rmd = store_thm ("alld_rmd",
``!l l'.(rmDupes l = l') ==> ALL_DISTINCT l'``,
Induct_on `l` THEN SRW_TAC [] [rmDupes] THEN
SRW_TAC [] [ALL_DISTINCT] THENL[
METIS_TAC [rmd_del, not_mem_delete, rmd_r2],
SRW_TAC [] [rmd_del] THEN
`?l'.rmDupes l = l'` by METIS_TAC [] THEN
ASM_REWRITE_TAC [] THEN
METIS_TAC [alld_delete]])

val diff_thm = store_thm(
  "diff_thm",
  ``(diff l1 [] = l1) ∧
    (diff l1 (h::t) = diff (delete h l1) t)``,
  Cases_on `l1` THEN SRW_TAC [][diff, delete] THENL [
    Cases_on `t` THEN SRW_TAC [][diff],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][delete_not_mem1]
  ]);

val MEM_delete = store_thm(
  "MEM_delete",
  ``MEM e (delete h l) = e ≠ h ∧ MEM e l``,
  Induct_on `l` THEN SRW_TAC [][delete] THEN METIS_TAC []);

val diff_mem = store_thm ("diff_mem",
``!e l1 l2. MEM e (diff l1 l2) = MEM e l1 /\ ~(MEM e l2)``,
Induct_on `l2` THEN SRW_TAC [][diff_thm, MEM_delete] THEN METIS_TAC []);

val diff_mem1 = store_thm ("diff_mem1",
``!e l1 l2.MEM e (diff l1 l2) ==> MEM e l1 /\ ~(MEM e l2)``,
METIS_TAC [diff_mem]);

val diff_mem2 = store_thm ("diff_mem2",
``!e l1 l2.MEM e l1 ==> ~(MEM e l2) ==> MEM e (diff l1 l2)``,
METIS_TAC [diff_mem]);

val diff_DIFF = store_thm ("diff_DIFF",
``!l1 l2. set (diff l1 l2) = (set l1) DIFF (set l2)``,
SRW_TAC [] [EXTENSION, diff_mem]);

val len1 = store_thm ("len1",
``!l1 l1' rst rst'.(l1++rst = l1'++rst') ==> (LENGTH l1 = LENGTH l1') ==> (l1 = l1')``,
Induct_on `l1` THEN Induct_on `l1'` THEN SRW_TAC [] [] THEN
METIS_TAC [])


val len2 = store_thm ("len2",
``!l1 l1' rst rst'.(l1++rst = l1'++rst') ==> (LENGTH l1' < LENGTH l1) ==> ?pfx sfx.(l1=pfx++sfx) /\ (l1'=pfx)``,
Induct_on `l1` THEN Induct_on `l1'` THEN SRW_TAC [] [] THEN
METIS_TAC [])

val len3 = store_thm ("len3",
``!l1 l1' rst rst'.(l1++rst = l1'++rst') ==> (LENGTH l1' > LENGTH l1) ==> ?pfx sfx.(l1'=pfx++sfx) /\ (l1=pfx)``,
Induct_on `l1` THEN Induct_on `l1'` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
`LENGTH l1' > LENGTH l1` by FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [])


val listStartSame = store_thm ("listStartSame",
			       ``!l l1 l1'.((l++l1) = (l++l1')) ==> (l1=l1')``,
Induct_on `l` THEN SRW_TAC [] [])





val list_mem1 = store_thm ("list_mem1",
``!l.~(l=[]) = ?e.MEM e l``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM, list_exists_mem])

val list_mem2 = store_thm ("list_mem2",
``!l.~(l=[]) = ?h t.(l=h::t)``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM])

val last_elem = store_thm ("last_elem",
``!l pfx e. (l = pfx ++ [e]) ==> (LAST l = e)``,
Induct_on `pfx` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [LAST_DEF])

val cx = store_thm ("cx",
``!stl pfx h e t sfx.~(h=e) ==> ~(stl ++ [e] = pfx ++ stl ++ h::t ++ sfx)``,
SRW_TAC [][] THEN STRIP_TAC THEN
FIRST_ASSUM (ASSUME_TAC o AP_TERM ``LENGTH``) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH pfx = 0) ∧ (LENGTH t = 0) ∧ (LENGTH sfx = 0)` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]);

val pop_eq = store_thm ("pop_eq",
``!l n.(LENGTH l = n) ==> (pop l n = [])``,
Induct_on `l` THEN SRW_TAC [] [pop] THEN
FULL_SIMP_TAC (arith_ss) [])

val c0 = store_thm ("c0",
``!pfx stl l.(pfx ++ l = REVERSE (MAP FST (MAP FST stl)))  ==>
(REVERSE (MAP FST (MAP FST (pop stl (LENGTH l)))) = pfx)``,
SRW_TAC [] [] THEN
`(MAP FST (MAP FST (pop stl (LENGTH l)))) = pop (MAP FST (MAP FST stl)) (LENGTH l)` by METIS_TAC [map_pop] THEN
ONCE_ASM_REWRITE_TAC [] THEN
`(MAP FST (MAP FST stl)) = REVERSE (pfx++l)` by METIS_TAC [REVERSE_REVERSE] THEN
FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
METIS_TAC [popnthm, REVERSE_REVERSE, rev_len])


val last_append = store_thm ("last_append",
``!l1 l2.~(l2=[]) ==> (LAST (l1++l2) = LAST l2)``,
SRW_TAC [] [] THEN
`?h t.l2=h::t` by METIS_TAC [list_mem2] THEN
SRW_TAC [] [LAST_DEF] THEN
Induct_on `l1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [LAST_DEF])


val pfxthm2 = store_thm ("pfxthm2",
``!r1 sfx.(IS_PREFIX r1 (r1 ++ sfx) ==> (sfx=[]))``,
Induct_on `r1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
Induct_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [IS_PREFIX])

val elem_eq = store_thm ("elem_eq",
``!l1 l2 l3 e h.(l1++[e]++l2 = l1++[h]++l3) ==> (e=h)``,
Induct_on `l1` THEN SRW_TAC [] [] THEN
METIS_TAC [])


val lastElemEq = store_thm ("lastElemEq",
``!l l' e e'.(l++[e] = l'++[e']) ==> (e=e')``,
Induct_on `l` THEN Induct_on `l'` THEN SRW_TAC [] [])

val lastListBdown = store_thm ("lastListBdown",
``!l e.~(l=[]) ==> (LAST l = e) ==> ?pfx.(l=pfx++[e])``,
Induct_on `l` THEN SRW_TAC [] [LAST_DEF] THEN
METIS_TAC [APPEND])

val listEq = store_thm ("listEq",
``!l l1.(l = l1 ++ l) =  (l1=[])``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH t = LENGTH (t' ++ h::t)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
DECIDE_TAC)

val pop_not_empty = store_thm ("pop_not_empty",
``!l n.(LENGTH l > n) ==> ~(pop l n = [])``,
Induct_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
SRW_TAC [] [pop] THEN
`LENGTH l > n-1` by FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [])

val twoListAppEq = store_thm("twoListAppEq",
``(l1++rst = l1'++rst') ==>
   ((l1=l1') /\ (rst=rst')) \/
   (?s1' s2'.(l1=l1'++s1') /\ (rst=s2') /\ (rst'=s1'++s2')) \/
   (?s1 s2.(l1'=l1++s1) /\ (rst'=s2) /\ (rst=s1++s2))``,
Cases_on `LENGTH l1' < LENGTH l1` THEN
SRW_TAC [] []
THENL[

      `?pfx sfx.(l1=pfx++sfx) /\ (l1'=pfx)` by METIS_TAC [len2] THEN
      SRW_TAC [] [] THEN
      Cases_on `sfx` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `h::t++rst=rst'` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [],

      `(LENGTH l1' = LENGTH l1) \/
		 (LENGTH l1' > LENGTH l1)` by DECIDE_TAC
      THENL[
	    METIS_TAC [len1, APPEND_11],

	    `?pfx sfx.(l1'=pfx++sfx) /\ (l1=pfx)` by METIS_TAC [len3] THEN
	    SRW_TAC [] [] THEN
	    `rst=sfx++rst'` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    ]
      ])

val isSuffix = Define
`isSuffix x l = IS_PREFIX  (REVERSE l)  (REVERSE x)`

val x = store_thm ("x",
``!e t.((e::t) = t++[e']) ==> (e=e')``,
Induct_on `t` THEN SRW_TAC [] [] THEN METIS_TAC [])


val len_snoc = store_thm("len_snoc",
  ``!n. (LENGTH l = SUC n) = (?pfx t. (l = pfx ++ [t]) /\ (LENGTH pfx = n))``,
  Induct_on `l` THEN SRW_TAC [][] THEN
  Cases_on `n` THEN SRW_TAC [][LENGTH_NIL] THEN
  SRW_TAC [][EQ_IMP_THM] THENL [
    MAP_EVERY Q.EXISTS_TAC [`h::pfx`, `t`] THEN SRW_TAC [][],
    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC []
  ])


val isSuffix_APPEND = store_thm(
  "isSuffix_APPEND",
  ``!l1 l2. isSuffix l1 l2 = ?l0. l2 = l0 ++ l1``,
  SIMP_TAC (srw_ss()) [isSuffix, IS_PREFIX_APPEND] THEN
  SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [EQ_IMP_THM] THEN
  REPEAT STRIP_TAC THENL [
    `l2 = REVERSE l ++ l1` by METIS_TAC [REVERSE_APPEND,
					 REVERSE_REVERSE]THEN
    METIS_TAC [],
    SRW_TAC [][REVERSE_APPEND]
  ]);

val isSuffix_refl = store_thm(
  "isSuffix_refl",
  ``isSuffix s1 s1``,
  SRW_TAC [][isSuffix_APPEND] THEN METIS_TAC [APPEND]);
val _= export_rewrites ["isSuffix_refl"]

val isSuffix_lemma = store_thm(
  "isSuffix_lemma",
  ``isSuffix m2 (m1 ++ m2)``,
  METIS_TAC [isSuffix_APPEND])
val _ = export_rewrites ["isSuffix_lemma"]

val append_eq_imp_sfx = store_thm("append_eq_imp_sfx",
  ``!l1 l2 m1 m2. (l1 ++ l2 = m1 ++ m2) ==>
                  isSuffix l2 m2 \/ isSuffix m2 l2``,
  Induct THEN SRW_TAC [][] THEN
  Cases_on `m1` THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN METIS_TAC [APPEND, isSuffix_lemma],
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val append_eq_imp_pfx = store_thm("append_eq_imp_pfx",
  ``!l1 l2 m1 m2. (l1 ++ l2 = m1 ++ m2) ==>
                  IS_PREFIX l1 m1 \/ IS_PREFIX m1 l1``,
  Induct THEN SRW_TAC [][IS_PREFIX_NIL] THEN
  Cases_on `m1` THENL [
    SRW_TAC [][IS_PREFIX_NIL],
    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN SRW_TAC [][] THEN
    METIS_TAC []
  ]);



val c1 = store_thm ("c1",
``!pfx sfx.pfx++[e]++sfx = pfx++e::sfx``,
Induct_on `pfx` THEN SRW_TAC [] [])

val listEqRightAppend = store_thm ("listEqRightAppend",
``!l l1.(l = l ++ l1) ==> (l1=[])``,
Induct_on `l1` THEN SRW_TAC [] [] THEN
Cases_on `~(l = l ++ h::l1)` THEN SRW_TAC [] [] THEN
`LENGTH l = LENGTH (l ++ (h::l1))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (arith_ss) [])



val popAdd = store_thm ("popAdd",
``!l n rst.(LENGTH l >= n) ==>
  !rst.pop (l++rst) n = pop l n ++ rst``,
Induct_on `l` THEN SRW_TAC [] [pop]
THENL[
      `n=0` by DECIDE_TAC THEN
      Cases_on `rst` THEN
      FULL_SIMP_TAC (srw_ss()) [pop],

      `LENGTH l >= n-1` by DECIDE_TAC THEN
      METIS_TAC []])


val isSuffix_NIL2 = store_thm(
  "isSuffix_NIL2",
  ``!list.isSuffix list [] = (list = [])``,
  Induct_on `list` THEN SRW_TAC [][isSuffix, IS_PREFIX] THEN
  FULL_SIMP_TAC (srw_ss()) [isSuffix, IS_PREFIX_APPEND]);
val _ = export_rewrites ["isSuffix_NIL2"]

val memTl = store_thm
("memTl",
``!l.~(l = []) ==>
!e.(MEM e (TL l) ==> MEM e l )``,
Induct_on `l` THEN SRW_TAC [][])


val listHdTl = store_thm
("listHdTl",
``!l.~(l=[]) ==> (l=[HD l]++(TL l))``,
Induct_on `l` THEN SRW_TAC [][])

val flatMemNot = store_thm
("flatMemNot",
``!l' e.(!l.MEM l l' ==> ~MEM e l) ==>
~MEM e (FLAT l')``,
Induct_on `l'` THEN SRW_TAC [][]);

val last_exists = store_thm
("last_exists",
``∀l.l ≠ [] ⇒ ∃x.LAST l = x``,
Induct_on `l` THEN SRW_TAC [][]);

val frontLen = store_thm
("frontLen",
``∀l.(l≠[]) ⇒ LENGTH (FRONT l) < LENGTH l``,
Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []);

val frontAppendFst = store_thm
("frontAppendFst",
``FRONT (l ++ [x]) = l``,

Induct_on `l` THEN SRW_TAC [][FRONT_DEF]);


val elTlEq = store_thm
("elTlEq",
``∀t n.n + 1 < SUC (LENGTH t)
     ⇒
   (EL n t = EL (n+1) (h::t))``,

Induct_on `n` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
FULL_SIMP_TAC (arith_ss) [] THEN
`LENGTH t ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
`0 < LENGTH t` by DECIDE_TAC THEN
`LENGTH (TL t) = LENGTH t - 1` by METIS_TAC [LENGTH_TL] THEN
 `n+1 < SUC (LENGTH (TL t))` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [DECIDE ``n+1 = SUC n``]);


val elMemLen = store_thm
("elMemLen",
``∀n l. n < LENGTH l ⇒ ∃p s.(l = p++[EL n l]++s) ∧ (LENGTH p = n)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [APPEND_NIL, LENGTH, APPEND] THEN
RES_TAC THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 MAP_EVERY Q.EXISTS_TAC [`h::p`,`s`] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) []);

val listPairExists = store_thm
("listPairExists",
``∀l.∃l'.(l=MAP FST l') ∧ (l = FLAT (MAP SND l')) ∧
  (∀a b.MEM (a,b) l' ⇒  (LENGTH b = 1) ∧ (a=HD b))``,

Induct_on `l` THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `(h,[h])::l'` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);

val mapFstEq = store_thm
("mapFstEq",
``∀l r1 x r2.(MAP SND l = r1 ++ [x] ++ r2) ⇒ (l≠[]) ⇒
  (MAP FST l =
    MAP FST (TAKE (LENGTH r1) l) ++
    [FST (HD (DROP (LENGTH r1) l))] ++
    MAP FST (DROP (1 + LENGTH r1) l))``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`t`,`x`,`r2`] MP_TAC) THEN SRW_TAC [][]);

val mapSndTakeEq = store_thm
("mapSndTakeEq",
``∀l r1' x r2'.
(MAP SND l = r1' ++ [x] ++ r2')
⇒
(MAP SND (TAKE (LENGTH r1') l) = r1')``,

Induct_on `l` THEN SRW_TAC [][] THEN1
METIS_TAC [LENGTH_NIL] THEN
Cases_on `r1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC []);

val mapSndDropEq = store_thm
("mapSndDropEq",
``∀l r1' x r2'.
(MAP SND l = r1' ++ [x] ++ r2')
⇒
((MAP SND (DROP (1 + LENGTH r1') l)) = r2')``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `r1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC [DECIDE ``SUC t = 1 + t``]);

val flatMem = store_thm
("flatMem",
``∀l s1 s2 x. (FLAT l = s1++[x]++s2) ⇒
              ∃p s p' s'.
                  (l = p ++ [p'++[x]++s'] ++s) ∧
                  (s1=FLAT p++p') ∧
                  (s2=s'++FLAT s)``,
Induct_on `l` THEN SRW_TAC [][] THEN
IMP_RES_TAC twoListAppEq THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

  MAP_EVERY Q.EXISTS_TAC [`[]`,`l`,`s1`,`[]`] THEN
  SRW_TAC [][],

  MAP_EVERY Q.EXISTS_TAC [`[]`,`l`,`s1`,`s1'`] THEN
  SRW_TAC [][],

  IMP_RES_TAC twoListAppEq THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL[

    FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`s2`,`x`] MP_TAC) THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [FLAT_APPEND] THEN
    MAP_EVERY Q.EXISTS_TAC [`[h]++p`,`s`,`[]`,`s'`] THEN
    SRW_TAC [][],

    FIRST_X_ASSUM (Q.SPECL_THEN [`s1''`,`s2`,`x`] MP_TAC) THEN SRW_TAC [][] THEN
    MAP_EVERY Q.EXISTS_TAC [`[h]++p`,`s`,`p'`,`s'`] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    Cases_on `s1''` THEN (* bug here???  FULL_SIMP_TAC (srw_ss()) [] fails *)
    FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss [] THENL[
      FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`s2`,`x`] MP_TAC) THEN SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`[s1]++p`,`s`,`[]`,`s'`] THEN
      FULL_SIMP_TAC (srw_ss()) [],

      FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`s2`,`x`] MP_TAC) THEN SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`[]`,`l`,`s1`,`[]`] THEN
      FULL_SIMP_TAC (srw_ss()) []
    ]
  ]
]);

val mapDrop = store_thm
("mapDrop",
``∀l n.MAP SND (DROP n l) = DROP n (MAP SND l)``,

Induct_on `l` THEN SRW_TAC [][]);

val dropLen = store_thm
("dropLen",
``∀l l1 l2.(l = l1 ++ l2) ∧ (LENGTH l1 ≤ LENGTH l) ⇒
   (DROP (LENGTH l1) l = l2)`` ,

Induct_on `l` THEN SRW_TAC [][] THEN1
METIS_TAC [LENGTH_NIL,APPEND_NIL] THEN
Cases_on `l1` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []);


val dropNotNil = store_thm
("dropNotNil",
``∀l n.n < LENGTH l ⇒ (DROP n l ≠ [])``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []);

val everyFlat = store_thm(
"everyFlat",
``∀l1 l2 x.EVERY P (FLAT (l1++[x]++l2)) ⇒ EVERY P x``,

SRW_TAC [][EVERY_MEM,MEM_FLAT]);

val everyNotTwice = store_thm
("everyNotTwice",
``EVERY ($~ o $~ o isTmnlSym) v = EVERY isTmnlSym v``,

Induct_on `v` THEN SRW_TAC [][]);

val rmdNil = store_thm
("rmdNil",
``∀l.(rmDupes l = []) ⇔ (l=[])``,

Induct_on `l` THEN SRW_TAC [][rmDupes]);


val notMem_delete_len = store_thm
("notMem_delete_len",
``∀l.¬MEM e l ⇒ (LENGTH l = LENGTH (delete e l))``,

Induct_on `l` THEN SRW_TAC [][delete]);


val rmdNotMemLen = store_thm
("rmdNotMemLen",
``∀l.¬MEM e l ⇒
 LENGTH (rmDupes l) < LENGTH (rmDupes (e::l))``,

Induct_on `l` THEN SRW_TAC [][rmDupes] THEN
FULL_SIMP_TAC (srw_ss()) [rmd_del,rmDupes] THEN
SRW_TAC [][delete] THEN
`(delete e (delete h (rmDupes l))) =
(delete h (delete e (rmDupes l)))` by METIS_TAC [delete_diff_elem] THEN
ONCE_ASM_REWRITE_TAC[] THEN
`¬MEM e (rmDupes l)` by METIS_TAC [rmd_r2] THEN
`(delete e (rmDupes l)) = rmDupes l` by METIS_TAC [delete_not_mem] THEN
ONCE_ASM_REWRITE_TAC[] THEN
DECIDE_TAC);

val addFront = Define `addFront l e = l++e`;

val addlast = Define `addLast l e = l++e`;

val addFrontMem = store_thm
("addFrontMem",
 ``∀e.MEM e (MAP (addFront rhs) l)
 ⇒ ∃sfx.MEM sfx l ∧ (e=rhs++sfx)``,

Induct_on `l` THEN SRW_TAC [][addFront] THEN
METIS_TAC []);


val addFrontLast = store_thm
("addFrontLast",
``∀l.(l≠[])  ⇒ (LAST (MAP (addFront rhs) l ) = rhs++LAST l)``,

Induct_on `l` THEN SRW_TAC [][addFront] THEN
Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`MAP (addFront rhs) l ≠[]` by
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
METIS_TAC [last_append,APPEND,MEM]);



val addFrontDrop = store_thm
("addFrontDrop",
``∀dl.(dl = MAP (DROP (LENGTH rhs)) (MAP (addFront rhs) dl))``,

Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][addFront] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND]);

val addFrontImpDrop = store_thm
("addFrontImpDrop",
``∀dl.(MAP (addFront rhs) dl = l) ⇒ (dl = MAP (DROP (LENGTH rhs)) l)``,

Induct_on `dl` THEN SRW_TAC [][] THEN
SRW_TAC [][addFront] THEN1
METIS_TAC [BUTFIRSTN_LENGTH_APPEND] THEN
METIS_TAC [addFrontDrop]);


val addFrontAppList = store_thm
("addFrontAppList",

 ``∀dl'.(MAP (addFront rhs) dl' = p ++ [rhs ++r'++ [NTS B] ++ sfx] ++ s) ∧
    EVERY isTmnlSym (rhs++r') ∧ MEM (rhs ++r' ++ v++[NTS B] ++ w ++ sfx) s
    ⇒
    ∃p' s'.(dl' = p'++[r'++[NTS B]++sfx]++s') ∧ MEM (r'++v++[NTS B]++w++sfx) s'``,

SRW_TAC [][] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(Q.EXISTS_TAC `[]` THEN
Q.EXISTS_TAC `MAP (DROP (LENGTH rhs)) s` THEN
SRW_TAC [][] THEN
IMP_RES_TAC addFrontImpDrop THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [addFrontImpDrop,MAP_APPEND,APPEND_ASSOC,BUTFIRSTN_LENGTH_APPEND,
 APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND,APPEND_ASSOC]) THEN
Q.EXISTS_TAC `DROP (LENGTH rhs) h::MAP (DROP (LENGTH rhs)) t` THEN
Q.EXISTS_TAC `MAP (DROP (LENGTH rhs)) s` THEN
SRW_TAC [][] THEN
IMP_RES_TAC addFrontImpDrop THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [addFrontImpDrop,MAP_APPEND,APPEND_ASSOC,BUTFIRSTN_LENGTH_APPEND,
APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND,APPEND_ASSOC]);

val rmdAPPr = store_thm(
  "rmdAPPr",
  ``∀l s. LENGTH (rmDupes l) ≤ LENGTH (rmDupes (l ++ s))``,
  HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [][rmDupes, delete_append]);

fun introfy th = SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO] th

val rmdAPPl = store_thm
("rmdAPPl",
 ``∀p l. LENGTH (rmDupes l) ≤ LENGTH (rmDupes (p ++ l))``,
 SRW_TAC [][rmDupes_lts_card] THEN MATCH_MP_TAC (introfy CARD_SUBSET) THEN
 SRW_TAC [][SUBSET_DEF, rmd_mem_list]);

val rmdLenLe = store_thm
("rmdLenLe",
``∀l p s. LENGTH (rmDupes l) ≤ LENGTH (rmDupes (p++l++s))``,
SRW_TAC [][] THEN
METIS_TAC [DECIDE ``a≤ b ∧ b≤ c ⇒ a≤ c``,rmdAPPl,rmdAPPr]);

val notMemRmDLen = store_thm
("notMemRmDLen",
``∀X P X SF.
    ¬MEM e (rmDupes X) ⇒
    SUC (LENGTH (rmDupes X)) ≤ LENGTH (rmDupes (P ++ e::X ++ SF))``,
 SRW_TAC [][rmDupes_lts_card, DECIDE ``SUC x ≤ y ⇔ x < y``, rmd_mem_list] THEN
 MATCH_MP_TAC (introfy CARD_PSUBSET) THEN
 SRW_TAC [][PSUBSET_DEF, SUBSET_DEF, rmd_mem_list] THEN
 SRW_TAC [][EXTENSION, rmd_mem_list] THEN Q.EXISTS_TAC `e` THEN SRW_TAC [][]);

val memdel = store_thm
("memdel",
``∀l.MEM e (delete h l) ⇒ MEM e l``,

Induct_on `l` THEN SRW_TAC [][delete] THEN
METIS_TAC []);

val lpow = Define `lpow l i = REPLICATE i l`;

val _ = overload_on ("FLAT (lpow l i)", ``pow l i``)

val flatRepSuc = store_thm
("flatRepSuc",
``∀p i.FLAT (lpow p (SUC i)) = p++FLAT (lpow p i)``,

Induct_on `i` THEN SRW_TAC [][] THEN
SRW_TAC [][lpow, REPLICATE] THEN
`1=SUC 0`by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][REPLICATE]);


val flatRepComm = store_thm
("flatRepComm",
``∀i p.p++FLAT (lpow p i) =  FLAT (lpow p i)++p``,

Induct_on `i` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lpow,REPLICATE]);


val dropLast = Define
`dropLast sfx l = REVERSE (DROP (LENGTH sfx) (REVERSE l))`;

val listsec = Define
    `listsec front back l =
	     (dropLast back) ((DROP (LENGTH front)) l)`;


val listsecPfxSfx = store_thm
("listsecPfxSfx",
 ``∀m.(listsec p s (p++m++s) = m)``,
 SRW_TAC [][listsec,dropLast] THEN
 `(DROP (LENGTH p) (p ++ m ++ s)) = m++s`
 by METIS_TAC [BUTFIRSTN_LENGTH_APPEND,APPEND_ASSOC] THEN
 ONCE_ASM_REWRITE_TAC[] THEN
 SRW_TAC [][REVERSE_APPEND] THEN
 METIS_TAC [LENGTH_REVERSE, REVERSE_REVERSE,BUTFIRSTN_LENGTH_APPEND]);

val listsecDropNilSfx = store_thm
("listsecDropNilSfx",
``listsec p [] (p++x) = x``,

SRW_TAC [][listsec,dropLast] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND]);


val listsecLast = store_thm
("listsecLast",
``∀l.
(LAST l =p ++ ml ++ s) ∧ (l≠[]) ∧
(∀e.MEM e l ⇒ ∃m. m ≠ [] ∧ (e = p ++ m ++ s))
⇒
(LAST (MAP (listsec p s) l) = ml)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `l=[]`THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][listsecPfxSfx] THEN1
METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
`(LAST l = p ++ ml ++ s)` by METIS_TAC [APPEND,last_append] THEN
METIS_TAC [MAP_EQ_NIL,APPEND,last_append]);

val addFrontListsec = store_thm
("addFrontListsec",
``∀t.(∀e.MEM e t ⇒ ∃rst.(e=s1++rst)) ⇒
 (MAP (addFront s1) (MAP (listsec s1 []) t) = t)``,

Induct_on `t` THEN SRW_TAC [][addFront, listsec, dropLast] THEN
`∃rst.h = s1++rst` by METIS_TAC [] THEN
SRW_TAC [][] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND]);

val addLastListsec = store_thm
("addLastListsec",
 ``∀t. (∀e. MEM e t ⇒ ∃rst. e = rst ++ sfx) ⇒
 (MAP (λl. l ++ sfx) (MAP (listsec [] sfx) t) = t)``,

Induct_on `t` THEN SRW_TAC [][listsec, dropLast] THEN
`∃rst. h = rst ++ sfx` by METIS_TAC [] THEN
SRW_TAC [][REVERSE_APPEND]  THEN
METIS_TAC [REVERSE_REVERSE, BUTFIRSTN_LENGTH_APPEND, LENGTH_REVERSE]);


val addLastImpListsec = store_thm
("addLastImpListsec",
``∀l l'.(MAP (λl. l ++ s2) l = l') ⇒ (l = MAP (listsec [] s2) l')``,

Induct_on `l` THEN SRW_TAC [][listsec] THEN
FULL_SIMP_TAC (srw_ss()) [listsec, dropLast, REVERSE_APPEND]  THEN
METIS_TAC [LENGTH_REVERSE, REVERSE_REVERSE, BUTFIRSTN_LENGTH_APPEND]);


val listsecSame = store_thm
("listsecSame",
 ``∀l.(∀e.MEM e l ⇒ ∃rst.(e = v ++ rst ++ y)) ⇒
(MAP (listsec v []) (MAP (listsec [] y) l) = MAP (listsec v y) l)``,

Induct_on `l` THEN SRW_TAC [][listsec, dropLast, addFront] THEN
`∃rst. h = v ++ rst ++ y` by METIS_TAC [] THEN
SRW_TAC [][REVERSE_APPEND] THEN
METIS_TAC [REVERSE_REVERSE, BUTFIRSTN_LENGTH_APPEND, LENGTH_REVERSE,
	   REVERSE_APPEND, APPEND_ASSOC]);


val allDLenDel = store_thm
("allDLenDel",
``∀l. ALL_DISTINCT l ∧ MEM h l ⇒ (SUC (LENGTH (delete h l)) = LENGTH l)``,

Induct_on `l` THEN SRW_TAC [][delete] THEN
METIS_TAC [notMem_delete_len]);

val listDivLen = store_thm
("listDivLen",
``∀n l. n < LENGTH l ⇒
∃l1 l2 j.(l = l1 ++ l2) ∧ (LENGTH l1 = n) ∧ (LENGTH l2 = j)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND, APPEND_NIL, LENGTH]);

val memImpEl = store_thm
("memImpEl",
``∀s0. MEM n s0 ⇒ ∃i. i < LENGTH s0 ∧ (EL i s0 = n)``,

Induct_on `s0` THEN SRW_TAC [][] THEN1
(Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `SUC i` THEN
SRW_TAC [][]);

val elDrop = store_thm
("elDrop",
``∀i l. e ∈ l ∧ i < LENGTH l ∧ (∀j. j ≤ i ⇒ EL j l ≠ e) ⇒
e ∈ DROP (SUC i) l``,

SRW_TAC [][] THEN
IMP_RES_TAC listDivLen THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
(IMP_RES_TAC memImpEl THEN
`i ≤ LENGTH l1` by DECIDE_TAC THEN
METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
	   ⇒ j < l``])  THEN
`SUC (LENGTH l1) ≤ LENGTH (l1 ++ l2)` by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
`SUC (LENGTH l1) = 1 + LENGTH l1`by DECIDE_TAC THEN
`¬(e ∈ DROP 1 (DROP (LENGTH l1) (l1 ++ l2)))` by METIS_TAC [BUTFIRSTN_BUTFIRSTN] THEN
FULL_SIMP_TAC (srw_ss()) [BUTFIRSTN_LENGTH_APPEND] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
SRW_TAC [][] THEN
`LENGTH l1 ≤ LENGTH l1` by DECIDE_TAC THEN
METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
	   NOT_CONS_NIL,CONS]);


val takeSubset= store_thm
("takeSubset",
``∀l n. n ≤ LENGTH l ⇒
 set (TAKE n l) ⊆ set l``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
METIS_TAC []);

val allDNotMem = store_thm
("allDNotMem",
``∀l. ¬ALL_DISTINCT l ⇔ 
 (∃e.e ∈ l ∧ ∃l1 l2 l3.(l = l1 ++ [e] ++ l2 ++ [e] ++ l3))``,

Induct_on `l` THEN SRW_TAC [][EQ_IMP_THM] THEN1
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL, MEM ,MEM_APPEND, rgr_r9eq] THEN1
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL, MEM ,MEM_APPEND, rgr_r9eq] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL, MEM ,MEM_APPEND, rgr_r9eq]);


val TAKE_mem = store_thm
("TAKE_mem",
``∀l n. n ≤ LENGTH l ⇒ (∀e. e ∈ (TAKE n l) ⇒ e ∈ l)``,

Induct_on `l`THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);


val allDTake = store_thm
("allDTake",
``∀l n. n ≤ LENGTH l ∧ ALL_DISTINCT l ⇒
ALL_DISTINCT (TAKE n l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
SPOSE_NOT_THEN ASSUME_TAC  THEN
METIS_TAC [TAKE_mem]);


val deleteAllD = store_thm
("deleteAllD",
``∀l.ALL_DISTINCT l ⇒ ALL_DISTINCT (delete h l)``,

Induct_on `l` THEN SRW_TAC [][delete, ALL_DISTINCT] THEN1
METIS_TAC [] THEN
METIS_TAC [MEM_delete]);

val rmDupesImpAllD = store_thm
("rmDupesImpAllD",
``∀l.ALL_DISTINCT (rmDupes l)``,

Induct_on `l` THEN SRW_TAC [][rmDupes, ALL_DISTINCT] THEN
METIS_TAC [rmd_del, not_mem_delete, deleteAllD]);


val allDistinctNewlist = store_thm
("allDistinctNewlist",
``∀l:α list. 
INFINITE (UNIV:'a set) ⇒
∃l'. LENGTH l' ≥ LENGTH l ∧ ALL_DISTINCT l' ∧ (set l ∩ set l' = {})``,

Induct_on `l` THEN SRW_TAC [][] THEN1
METIS_TAC [ALL_DISTINCT] THEN
`∃l'. LENGTH l' ≥ LENGTH l ∧ ALL_DISTINCT l' ∧
 (set l ∩ set l' = {})` by METIS_TAC [] THEN
`FINITE (set (h::l ++ l'))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
IMP_RES_TAC NOT_IN_FINITE THEN
`FINITE (set (x::h::l++l'))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`∃x'.x' ∉ set (x::h::l ++ l')` by METIS_TAC [NOT_IN_FINITE] THEN
Q.EXISTS_TAC `x'::x::delete h l'` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss())[] THEN1

(IMP_RES_TAC allDLenDel THEN
Cases_on `h ∈ l'`  THEN1
(RES_TAC THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`LENGTH (delete h l') = LENGTH l'` by METIS_TAC [notMem_delete_len] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN

FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [memdel, alld_delete, not_mem_delete]);


(*val _ =
val mlDir = ref ("./theoryML/");

 let open emitLib
 in emitML (!mlDir)
   ("listLemmas",
    OPEN ["num", "list", "set"]
    :: MLSIG "type num = numML.num"
    :: DEFN rmDupes
    :: DEFN breakAtElem
    :: DEFN push
    :: DEFN pop
    :: DEFN take1
    :: DEFN take
    :: DEFN LIST_TO_SET
    :: [])
 end;
*)

val _ = export_theory ();
