(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory;
open pred_setTheory grammarDefTheory reachableGrammarTheory
generatingGrammarTheory;

val _ = new_theory "reachGenGrammar";


val rugr = Define `rugr g g' = 
    ∃g0.usefulnts g g0 ∧
    (∀e.MEM e (rules g') ⇔ 
     e ∈ { rule l r | MEM (rule l r)  (rules g0) ∧ 
	  ∃a b. RTC (derives g0) [NTS (startSym g0)] (a++[NTS l]++b) }) ∧
    (startSym g = startSym g')`;


val thm4_2 = store_thm
("thm4_2",
 ``~(language g = {}) ∧ (rugr g g') ⇒ (language g = language g')``,

SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [rugr] THEN
`language g = language g0`by METIS_TAC [lemma4_1a] THEN
`rgr g0 g'` by 
 (Cases_on `g` THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_def, usefulnts_def, startSym_def]) THEN
METIS_TAC [thm4_2]);



val _ = export_theory ();