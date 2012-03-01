open HolKernel boolLib Parse bossLib

val _ = new_theory "prettyPrinting"

local open pdaEqCfgTheory homomorphismTheory closureTheory laeslafsTheory parseTreeTheory treeDerivTheory in end

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Closefix,
                  term_name = "LENGTH",
                  pp_elements = [TOK "BarLeft|", TM, TOK "|BarRight"]}

val _ = TeX_notation {hol = "BarLeft|", TeX = ("\\ensuremath{|}", 1)}
val _ = TeX_notation {hol = "|BarRight", TeX = ("\\ensuremath{|}", 1)}

val _ = set_fixity "=" (Infix (NONASSOC, 450))

val _ = remove_termtok { term_name = "\\/", tok = "∨"}

val _ = add_rule {block_style = (AroundSameName, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infixr 300,
                  term_name = "\\/",
                  pp_elements = [HardSpace 1, TOK "∨", BreakSpace(1,0)]}

val _ = remove_termtok { term_name = "=", tok = "="}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2)],
                  term_name = "=",
                  fixity = Infix(NONASSOC, 450)}

val _ = remove_termtok { term_name = "<=>", tok = "⇔" }
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "⇔", BreakSpace(1,2)],
                  term_name = "<=>",
                  fixity = Infix(NONASSOC, 100)}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "(BEGIN_ID_STILE)", TM, TOK "(END_ID_STILE)"],
                  term_name = "ID'",
                  fixity = Infix(NONASSOC, 450)}
val _ = overload_on ("ID'", ``\s0 m s1. ID m s0 s1``)

(* including some backticks `` ensures that this file gets processed with
   unquote*)

val _ = export_theory()
