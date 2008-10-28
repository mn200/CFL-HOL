open HolKernel boolLib bossLib Parse

val _ = new_theory "sublist"

val _ = Hol_datatype `tree = Lf | Nd of 'a => tree => tree`

val _ = set_trace "Unicode" 1

val fringe_def = Define`
  (fringe Lf = []) ∧
  (fringe (Nd x Lf t2) = x :: fringe t2) ∧
  (fringe (Nd x t1 Lf) = fringe t1 ++ [x]) ∧
  (fringe (Nd x t1 t2) = fringe t1 ++ fringe t2)
`;
val _ = export_rewrites ["fringe_def"]

val trev_def = Define`
  (trev Lf = Lf) ∧
  (trev (Nd x t1 t2) = Nd x (trev t2) (trev t1))
`;
val _ = export_rewrites ["trev_def"]

val inorder_def = Define`
  (inorder Lf = []) ∧
  (inorder (Nd x t1 t2)  = inorder t1 ++ [x] ++ inorder t2)
`;
val _ = export_rewrites ["inorder_def"]

val inorder_trev = store_thm(
  "inorder_trev",
  ``∀t. inorder (trev t) = REVERSE (inorder t)``,
  Induct THEN SRW_TAC [][listTheory.REVERSE_APPEND] THEN 
  SIMP_TAC bool_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]);

val sublist_def = Define`
  (sublist [] l = T) ∧
  (sublist (h::t) l = case l of [] -> F || h'::t' -> if h = h' then sublist t t'
                                                     else sublist (h::t) t')
                                                          
`;

val sublist_thm = store_thm(
  "sublist_thm",
  ``(sublist [] l = T) ∧
    (sublist l [] = (l = [])) ∧
    (sublist (h1::t1) (h2::t2) = if h1 = h2 then sublist t1 t2 
                                 else sublist (h1::t1) t2)``,
  SIMP_TAC (srw_ss()) [Once sublist_def] THEN 
  Cases_on `l` THEN SRW_TAC [][sublist_def]);
val _ = export_rewrites ["sublist_thm"]


val sublist_append2R = store_thm(
  "sublist_append2R",
  ``∀l1 l2. sublist l1 l2 ==> sublist l1 (l2 ++ l3)``,
  Induct_on `l2` THEN SRW_TAC [][] THEN 
  Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
  SRW_TAC [][] THEN METIS_TAC []);

val _ = overload_on ("<=", ``sublist``)

val sublist_refl = store_thm(
  "sublist_refl",
  ``l ≤ l``,
  Induct_on `l` THEN SRW_TAC [][]);

val sublist_characterised = store_thm(
  "sublist_characterised",
  ``∀h l1 l2. (h::l1) ≤ l2 = ∃p s. (l2 = p ++ [h] ++ s) ∧ l1 ≤ s``,
  completeInduct_on `LENGTH l2` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN 
  `(l2 = []) ∨ (∃l2h l2t. l2 = l2h :: l2t)` 
      by (Cases_on `l2` THEN SRW_TAC [][]) THEN 
  SRW_TAC [][] THENL [
    SRW_TAC [][EQ_IMP_THM] THENL [
      MAP_EVERY Q.EXISTS_TAC [`[]`, `l2t`] THEN SRW_TAC [][],
      `(p = []) ∨ (∃ph pt. p = ph :: pt)` 
         by (Cases_on `p` THEN SRW_TAC [][]) THEN 
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN 
      `(l1 = []) ∨ (∃lh lt. l1 = lh :: lt)`
         by (Cases_on `l1` THEN SRW_TAC [][]) THEN 
      SRW_TAC [][] THEN 
      `∃p1 s1. (s = p1 ++ [lh] ++ s1) ∧ lt ≤ s1`
         by METIS_TAC [DECIDE ``x < SUC (z + 1 + x)``] THEN 
      SRW_TAC [][] THEN 
      MAP_EVERY Q.EXISTS_TAC [`pt ++ [h] ++ p1`, `s1`] THEN 
      SRW_TAC [][]
    ],

    SRW_TAC [][EQ_IMP_THM] THENL [
      MAP_EVERY Q.EXISTS_TAC [`l2h::p`, `s`] THEN SRW_TAC [][],
      `(p = []) ∨ (∃ph pt. p = ph :: pt)` 
         by (Cases_on `p` THEN SRW_TAC [][]) THEN 
      SRW_TAC [][] THEN  FULL_SIMP_TAC (srw_ss()) [] THEN 
      SRW_TAC [][] THEN 
      METIS_TAC []
    ]
  ]);

val sublist_append2L = store_thm(
  "sublist_append2L",  
  ``∀l1 l2 l3. l1 ≤ l2 ==> l1 ≤ (l3 ++ l2)``,
  Cases_on `l2` THEN SRW_TAC [][] THEN 
  Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [sublist_characterised] THEN 
  Cases_on `h' = h` THEN SRW_TAC [][] THENL [
    METIS_TAC [listTheory.APPEND, listTheory.APPEND_ASSOC],
    FULL_SIMP_TAC (srw_ss()) [] THEN 
    MAP_EVERY Q.EXISTS_TAC [`l3 ++ [h] ++ p`, `s`] THEN 
    METIS_TAC [listTheory.APPEND, listTheory.APPEND_ASSOC]
  ]);

val sublist_CONS1_E = store_thm(
  "sublist_CONS1_E",
  ``(h::l1) ≤ l2 ==> l1 ≤ l2``,
  Cases_on `l2` THEN SRW_TAC [][] THENL [
    METIS_TAC [listTheory.APPEND, sublist_append2L],
    FULL_SIMP_TAC (srw_ss()) [sublist_characterised] THEN 
    METIS_TAC [listTheory.APPEND, sublist_append2L]
  ]);

val sublist_LENGTH = store_thm(
  "sublist_LENGTH",
  ``∀l1 l2. l1 ≤ l2 ⇒ LENGTH l1 ≤ LENGTH l2``,
  Induct_on `l2` THEN SRW_TAC [][] THEN 
  Cases_on `l1` THEN SRW_TAC [][] THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  Cases_on `h = h'` THEN SRW_TAC [][] THENL [
    SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [] THEN 
    RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
    DECIDE_TAC
  ]);

val sublist_APPEND_bothR = store_thm(
  "sublist_APPEND_bothR",
  ``∀l1 l2 l3. (l1 ++ l3) ≤ (l2 ++ l3) = l1 ≤ l2``,
  Induct_on `l2` THEN SRW_TAC [][] THENL [
    SRW_TAC [][EQ_IMP_THM, sublist_refl] THEN 
    IMP_RES_TAC sublist_LENGTH THEN 
    FULL_SIMP_TAC (srw_ss()) [] THEN 
    `LENGTH l1 = 0` by DECIDE_TAC THEN 
    METIS_TAC [listTheory.LENGTH_NIL],
    Cases_on `l1` THEN SRW_TAC [][] THENL [
      METIS_TAC [sublist_append2L, listTheory.APPEND, 
                 listTheory.APPEND_ASSOC, sublist_refl],
      METIS_TAC [listTheory.APPEND]
    ]
  ]);
    
val sublist_APPEND_TWICE = store_thm(
  "sublist_APPEND_TWICE",
  ``∀x y u v. x ≤ y ∧ u ≤ v ⇒ (x ++ u) ≤ (y ++ v)``,
  Induct_on `x` THEN 
  SIMP_TAC (srw_ss()) [sublist_append2L, sublist_append2R] THEN 
  SRW_TAC [][sublist_characterised] THEN 
  MAP_EVERY Q.EXISTS_TAC [`p`, `s ++ v`] THEN SRW_TAC [][]);
  

val fringe_sublist_inorder = store_thm(
  "fringe_sublist_inorder",
  ``∀t. fringe t ≤ inorder t``,
  Induct THEN SRW_TAC [][] THEN 
  Cases_on `t` THEN Cases_on `t'` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    SRW_TAC [][sublist_APPEND_bothR],
    METIS_TAC [sublist_APPEND_TWICE, sublist_append2R, 
               listTheory.APPEND_ASSOC]
  ]);
    
val _ = export_theory()
       
