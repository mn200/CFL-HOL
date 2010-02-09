open HolKernel Parse boolLib bossLib

open grammarDefTheory relationTheory listTheory

val gaw = gaw_def
val derives = derives_def

val _ = new_theory "uselessSymbols"

(*
Useless symbols
A symbol X is useful if there is a derivation S *=> aXb *=> w for some a,b,w where w in T*.
but have to handle the case where X may only occur in sentential forms containing a useless
symbol itself.
*)

(*
Lemma 4.2
Given a CFG G = (V T P S) we can effectively find an
equivalent CFG G' = (V', T', P', S) such that for each X in V'UT'
there exists a and b in (V'UT')* for which S=>*aXb.
*)


(*
Theorem 4.3

If L=L(G) for some CFG G = (V,T,P,S), then L-{e} is L(G') for a CFG G' with no useless symbols or e-productions.
*)

(*
 Lemma 4.3
Define an A-production to be a production with variable A on the
left. Let G=(V,T,P,S) be a CFG. Let A->xBy be a production in P and
B->b1|b2... be the set of all B-productions. Let G1=(V,T,P1,S) be
obtained from G by deleting the production A->xBy from P and adding
the productions A->xb1y|xb2y.... Then L(g)=L(G1).
*)





(*
Theorem 4.6
Every CFL L without e can be generated by a grammar for
which every production is of the form A->aalph, where A is a variable,
a is a terminal and alpha (possibly empty) is a string of variables.
*)

val sub_result = store_thm ("sub_result",
  ``∀g symlist.EVERY (gaw g) symlist ⇒
    ∃w. RTC (derives g) symlist w ∧ EVERY isTmnlSym w``,
STRIP_TAC THEN
  Induct_on `symlist` THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `[]` THEN SRW_TAC [][RTC_RULES],
    FULL_SIMP_TAC (srw_ss()) [gaw] THEN
    Q.EXISTS_TAC `w' ++ w` THEN SRW_TAC [] [] THEN
    `RTC (derives g) (h::symlist) (w' ++ w) = RTC (derives g) ([h]++symlist) (w' ++ w)` by SRW_TAC [] [] THEN
    ASM_REWRITE_TAC [] THEN METIS_TAC [derives_append]]);


val key_result = store_thm ("key_result",
  ``EVERY (gaw g) v ∧ derives g u v ⇒ EVERY (gaw g) u``,
  SRW_TAC [][derives] THEN
  FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND] THEN `EVERY (gaw g) rhs ⇒
    ∃w. RTC (derives g) rhs w ∧ EVERY isTmnlSym w` by FULL_SIMP_TAC (srw_ss()) [gaw,sub_result]
THEN RES_TAC THEN SRW_TAC [] [gaw] THEN
`∀lhs rhs g.MEM (rule lhs rhs) (rules g) ⇒ derives g [NTS lhs] rhs` by FULL_SIMP_TAC (srw_ss()) [res1]
THEN RES_TAC THEN METIS_TAC [RTC_RULES]);

val sub_result_rev = store_thm ("sub_result_rev",
``∀symlist.(∃w. RTC (derives g) symlist w ∧ EVERY isTmnlSym w) ⇒ EVERY (gaw g) symlist``,
Q_TAC SUFF_TAC `∀symlist w.RTC (derives g) symlist w ⇒ EVERY isTmnlSym w ⇒ EVERY (gaw g) symlist`
THEN1 METIS_TAC [] THEN HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] []
THENL [Induct_on `symlist` THEN SRW_TAC [] [gaw] THEN Q.EXISTS_TAC `[h]` THEN SRW_TAC [] [RTC_RULES],
METIS_TAC [key_result]]);

val term_syms_gen_words = store_thm ("term_syms_gen_words",
  ``EVERY isTmnlSym w ⇒ EVERY (gaw g) w``,
  METIS_TAC [RTC_RULES, sub_result_rev])

val _ = export_theory()
