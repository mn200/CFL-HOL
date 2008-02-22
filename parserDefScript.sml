(* Verification of ML-Yacc Parser
AB 25 Oct 2007
*)

(*
Functions
yacc :: grammar -> lrmachine option
parse:: lrmachine -> string -> parse option
*)

open HolKernel boolLib bossLib Parse BasicProvers Defn
open stringTheory relationTheory pred_setTheory listTheory  boolSimps optionTheory
open grammarDefTheory listLemmasTheory regexpTheory whileLemmasTheory
open setLemmasTheory parseTreeTheory containerTheory Defn arithmeticTheory whileTheory markerTheory boolLemmasTheory

val _ = new_theory "parserDef"


val _ = Hol_datatype `item = item of string => symbol list # symbol list`; (*  # symbol list`;*)

val _ = type_abbrev ("state", ``:item list``)

val _ = Hol_datatype `action = REDUCE of rule | GOTO of state | NA`

val stateSym = Define `stateSym (state sym itl) = sym`

val stateItl = Define `stateItl (state sym itl) = itl`


val mlDir = ref ("./theoryML/");

val _ =
 let open EmitML
 in emitML (!mlDir)
   ("parser",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: DATATYPE `item = item of string => symbol list # symbol list`
    :: DATATYPE `state = state of symbol => item list`
    :: DATATYPE `action = REDUCE of rule | GOTO of state | NA`
    :: DEFN stateItl
    :: DEFN stateSym
    (*:: DEFN yacc*)
    :: [])
 end;



val _ = export_theory ();

