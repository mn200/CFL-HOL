open HolKernel boolLib bossLib Parse BasicProvers

open arithmeticTheory

val _ = new_theory "arithmeticLemmas";

val _ = Globals.linewidth := 60

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val powLe  = store_thm
("powLe",
``∀n p p'.n ≤ 2**(p-1) ∧ (p ≤ p') ⇒ n ≤ 2**(p'-1)``,
SRW_TAC [][] THEN MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS THEN 
Q.EXISTS_TAC `2 ** (p - 1)` THEN SRW_TAC [][] THEN DECIDE_TAC);


val powMult = store_thm
("powMult",
``∀n.2*2**n = 2**(n+1)``,

Induct_on `n` THEN SRW_TAC [][] THEN
`SUC n + 1 = SUC (SUC n)` by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][Once EXP] THEN
METIS_TAC [EXP]);

val powGt0 = store_thm
("powGt0",
``∀n.n > 0 ⇒ 2 ** n > 0``,

 Induct_on `n` THEN SRW_TAC [][] THEN
 Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 `SUC (SUC n') = SUC n' + 1` by DECIDE_TAC THEN
 SRW_TAC [][] THEN
 `2**(SUC n' + 1) = 2*2**(SUC n')` by METIS_TAC [powMult] THEN
 SRW_TAC [][] THEN
 DECIDE_TAC);

val powGe2 = store_thm
("powGe2",
``∀n.2 * 2 ** n ≥ 2``,

Induct_on `n` THEN SRW_TAC [][] THEN
`SUC n = n + 1` by DECIDE_TAC THEN
`2 ** SUC n = 2 * 2 ** n` by METIS_TAC [powMult] THEN
FULL_SIMP_TAC (arith_ss) []);

val powGtTrans = store_thm
("powGtTrans",
``∀n k k0. n ≥ 2 ** k ∧ k0 ≤ k ∧ k0 ≥ 1 ∧ k ≠ 0 ⇒ n ≥ 2 ** k0``,

Induct_on `n` THEN SRW_TAC [][] THEN
Cases_on `k` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (`SUC n > 0` by DECIDE_TAC THEN
  `2 ** (SUC n) > 0` by METIS_TAC [powGt0] THEN
  DECIDE_TAC) THEN
Cases_on `k0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `n''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`SUC n' = (n' + 1)` by DECIDE_TAC THEN
`SUC n ≥ 2 * 2 ** n'` by METIS_TAC [powMult] THEN
`2 * 2 ** n' ≥ 2 ` by METIS_TAC [powGe2] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
SRW_TAC [][] THEN
MAGIC);


val _ = export_theory();