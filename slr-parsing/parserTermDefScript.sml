open HolKernel boolLib bossLib Parse BasicProvers Defn;

open listTheory containerTheory pred_setTheory arithmeticTheory
     relationTheory markerTheory boolSimps optionTheory;

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
     parseTreeTheory (* parserDefTheory *) yaccDefTheory ;

val _ = new_theory "parserTermDef";

(* Empty theory .... does this do something useful? *)

val _ = export_theory();



(*
``!g.(slr g = SOME m) ==> !sl stl csl.~(parser g (SOME m) sl stl csl = NONE)``,

SRW_TAC [] [parser_def, LET_THM]


*)
