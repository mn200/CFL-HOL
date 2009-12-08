(* A theory about boolean expressions *)
open HolKernel boolLib bossLib Parse boolSimps
open stringTheory containerTheory optionTheory
open pred_setTheory listTheory arithmeticTheory Defn

val _ = new_theory "boolLemmas";

val if_rw_SOMEeqSOME = store_thm ("if_rw_SOMEeqSOME",
``((if p then SOME x else NONE) = SOME x') = ((x=x') /\ p)``,
SRW_TAC [][AC CONJ_ASSOC CONJ_COMM])

(* I find it hard to believe this is useful *)
val if_rw_SOME = store_thm ("if_rw_SOME",
``?x' p'.(SOME x' = (if p then NONE else p')) = ((p'=SOME x'))``,
MAP_EVERY Q.EXISTS_TAC [`ARB`, `NONE`] THEN SRW_TAC [][]);

val option_case_rwt = store_thm("option_case_rwt",
  ``((case x of NONE -> NONE || SOME y -> f y) = SOME z) = (?a. (x = SOME a) /\ (f a = SOME z))``,
  Cases_on `x` THEN SRW_TAC [][]);

val list_case_rwt = store_thm("list_case_rwt",
  ``(((case x of [] -> NONE || h::t -> f h t) = SOME z) = (?i j. (x = i::j) /\ (f i j = SOME z))) /\

    (((case x of [] -> y || h::t -> NONE) = SOME z) = ((x = []) /\ (y = SOME z)))``,
  Cases_on `x` THEN SRW_TAC [][] );


val option_r1 = store_thm ("option_r1",
``!f.~(f=NONE) ==> (x=THE f) ==> ( SOME x = f)``,
SRW_TAC [] [] THEN
Cases_on `f` THEN
FULL_SIMP_TAC (srw_ss()) [THE_DEF]
)

val ih = prove(
``{ l | EVERY P l /\ LENGTH l <= SUC n } =
    [] INSERT BIGUNION (IMAGE (\t. IMAGE (\h. h :: t) { x | P x })
                              { l | EVERY P l /\ LENGTH l <= n })``,
SRW_TAC [DNF_ss][Once EXTENSION, EQ_IMP_THM] THEN
Cases_on `x` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
MAP_EVERY Q.EXISTS_TAC [`{ h'::t | P h'}`, `t`] THEN SRW_TAC [][]);

val finite_length_limited = prove(
``FINITE { x | P x } ==> !n. FINITE { l | EVERY P l /\ LENGTH l <= n }``,
STRIP_TAC THEN Induct THEN1 SRW_TAC [CONJ_ss][LENGTH_NIL] THEN
ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [ih]);

val every_list_to_set = prove(
``EVERY P l ==> LIST_TO_SET l SUBSET { x | P x}``,
Induct_on `l` THEN SRW_TAC [][]);

val all_distinct_lemma = prove(
``!l. ALL_DISTINCT l ==> (LENGTH l = CARD (LIST_TO_SET l))``,
Induct THEN SRW_TAC [][]);

val all_distinct_lemma2 = prove(
``FINITE { x | P x } ==>
{ l | EVERY P l /\ ALL_DISTINCT l } SUBSET
{ l | EVERY P l /\ LENGTH l <= CARD { x | P x } }``,
STRIP_TAC THEN SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
Induct THEN SRW_TAC [][] THEN
`LIST_TO_SET x SUBSET { x | P x}` by METIS_TAC [every_list_to_set] THEN
`~(LIST_TO_SET x = { x | P x})`
by (STRIP_TAC THEN
`~(h IN {x | P x})` by METIS_TAC [IN_LIST_TO_SET] THEN
FULL_SIMP_TAC (srw_ss()) []) THEN
`LIST_TO_SET x PSUBSET { x | P x}` by METIS_TAC [PSUBSET_DEF] THEN
`CARD (LIST_TO_SET x) < CARD { x | P x}` by METIS_TAC [CARD_PSUBSET] THEN
`LENGTH x <= CARD { x | P x}` by METIS_TAC [] THEN
`LENGTH x = CARD (LIST_TO_SET x)` by METIS_TAC [all_distinct_lemma] THEN
DECIDE_TAC);

val lemma = store_thm("lemma",
``FINITE { x | P x} ==> FINITE {l | EVERY P l /\ ALL_DISTINCT l}``,
METIS_TAC [SUBSET_FINITE, all_distinct_lemma2, finite_length_limited]);

val setc_flem = store_thm(
"setc_flem",
``FINITE P ==> FINITE { l | EVERY P l /\ ALL_DISTINCT l}``,
ASSUME_TAC lemma THEN
`{ x | P x} = P` by SRW_TAC [][EXTENSION, IN_DEF] THEN
FULL_SIMP_TAC (srw_ss()) []);

val _ = export_theory ();
