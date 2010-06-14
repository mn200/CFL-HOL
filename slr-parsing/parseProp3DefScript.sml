open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
parseTreeTheory yaccDefTheory

val _ = new_theory "parseProp3Def";
val _ = diminish_srw_ss ["list EQ"];

(* 3. There is an item rule in the current state list that has the
stack symbols as its pfx and by that it implies that a corresponding
rule exists in the grammar *)

val stackSymbols = Define 
`(stackSymbols [] = []) ∧
(stackSymbols (((sym itl), pt)::rst) = sym::stackSymbols rst)`;

val prop3  = Define `prop3 g stl = 
∀sym itl pt.MEM ((sym itl), pt) stl ⇒ isTmnlSym sym 
    ⇒ ∃e.(MEM e itl ∧ (∃nt sfx.(e=item nt (stackSymbols (TL stl), sfx))))`;


val prop3thm = store_thm ("prop3thm", 
``∀m g.(m=slr g) ⇒ prop3 g stl ⇒ 
((parse m (sl, stl, (state s itl::csl)) = SOME (sl',stl',csl'))) 
			  ⇒ prop3 g stl``,

FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM, prop3] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) 
[option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
(* 5 subgoals *)
METIS_TAC []
);

val _ = export_theory ();