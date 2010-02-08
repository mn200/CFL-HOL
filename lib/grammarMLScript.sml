open HolKernel Parse boolLib bossLib

open setLemmasTheory containerLemmasTheory
open symbolDefTheory grammarDefTheory

val _ = new_theory "grammarML"

val nonTerminals = nonTerminals_def
val terminals = terminals_def
val rule_nonterminals = rule_nonterminals_def
val rule_terminals = rule_terminals_def
val allSyms = allSyms_def

val nonTerminalsML =  Define
`(nonTerminalsML (G [] s) = {NTS s}) ∧
 (nonTerminalsML (G (rule l r::rs) s) =
      set (FILTER isNonTmnlSym (NTS l :: r)) ∪
      nonTerminalsML (G rs s))`;


val terminalsML = Define
`(terminalsML (G [] s) = LIST_TO_SET []) ∧
 (terminalsML (G (rule l r::rs) s) =
      LIST_TO_SET (FILTER isTmnlSym r) ∪ terminalsML (G rs s))`;

val nonTerminalsEq = store_thm
("nonTerminalsEq",
``nonTerminals g = nonTerminalsML g``,
Cases_on `g` THEN
Induct_on `l` THEN
SRW_TAC [] [nonTerminals, nonTerminalsML] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,nonTerminalsML,
			  isNonTmnlSym_def,nonTerminals] THEN
`nonTerminalsML (G l n) =
     NTS n INSERT BIGUNION (IMAGE rule_nonterminals (set l))`
	 by SRW_TAC [] [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [] [filter_seteq,insert_union,isNonTmnlSym_def]);


val terminalsEq = store_thm
("terminalsEq",
``terminals g = terminalsML g``,
Cases_on `g` THEN
Induct_on `l` THEN
SRW_TAC [] [terminals, terminalsML] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [terminalsML,isTmnlSym_def,terminals,
			  rule_terminals] THEN
`terminalsML (G l n) = BIGUNION (IMAGE rule_terminals (set l))`
				by SRW_TAC [] [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [filter_seteq,insert_union,
			  isTmnlSym_def]);

val allSymsML = Define
`allSymsML g = nonTerminalsML g ∪ terminalsML g`;


val allSymsEq = store_thm (
"allSymsEq",
``allSyms g = allSymsML g``,
SRW_TAC [][allSyms, allSymsML, terminalsEq, nonTerminalsEq]);

val _ = export_theory()
