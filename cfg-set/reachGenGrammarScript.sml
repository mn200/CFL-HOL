(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory;
open pred_setTheory grammarDefTheory reachableGrammarTheory generatingGrammarTheory;

val _ = new_theory "reachGenGrammar";


val rugr = Define `rugr g = G { rule l r | rule l r IN (rules (usefulnts g)) /\ ?a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)} (startSym g)`;

val eq_srugr = prove (
``startSym (rugr g) = startSym g``,
Cases_on `g` THEN METIS_TAC [startSym_def,rugr]
);


val thm4_2 = prove(
``~(language g = {}) ==> (language g = language (rgr (usefulnts g)))``,
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM] THENL
[
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def,eq_startsym,eq_srgr] THEN
`RTC (derives (usefulnts (G f s))) [NTS s] x'` by METIS_TAC [subr4] THEN
METIS_TAC [rgr_r7,startSym_def,eq_srgr,eq_startsym],
`RTC (derives (usefulnts g)) [NTS (startSym g)] x'` by METIS_TAC [rgr_subr3_rtc,startSym_def,eq_srgr,eq_startsym] THEN
METIS_TAC [subr4_rev]
]
);

val _ = export_theory ();