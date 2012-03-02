open HolKernel boolLib Parse bossLib

val _ = new_theory "prettyPrinting"

local open pdaEqCfgTheory homomorphismTheory closureTheory laeslafsTheory parseTreeTheory treeDerivTheory in end

val star_rules' = store_thm(
  "star_rules'",
  ``[] ∈ star A ∧
    (s ∈ A ⇒ s ∈ star A) ∧
    (s1 ∈ A ∧ s2 ∈ star A ⇒ s1 ++ s2 ∈ star A)``,
  Q.ISPEC_THEN `star A` MP_TAC pred_setTheory.SPECIFICATION THEN
  SRW_TAC [][symbolDefTheory.star_rules]);

val _ = overload_on ("RTC", ``star``)

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

val _ = overload_on ("ID'", ``\s0 m s1. ID m s0 s1``)
val _ = overload_on ("IDRTC", ``\s0 m s1. (ID m)^* s0 s1``);
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "(BEGIN_ID_STILE)", TM,
                                 TOK "(END_ID_STILE)", BreakSpace(1,2)],
                  term_name = "ID'",
                  fixity = Infix(NONASSOC, 450)}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "(BEGIN_IDRTC_STILE)", TM,
                                 TOK "(END_ID_STILE)", BreakSpace(1,2)],
                  term_name = "IDRTC",
                  fixity = Infix(NONASSOC, 450)}


val _ = overload_on ("ppderives", ``\sf0 g sf1. derives g sf0 sf1``);
val _ = overload_on ("pprtcderives", ``\sf0 g sf1. (derives g)^* sf0 sf1``);
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "(BEGIN_DERIVES)", TM,
                                 TOK "(END_DERIVES)", BreakSpace(1,2)],
                  term_name = "ppderives",
                  fixity = Infix(NONASSOC, 450)}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "(BEGIN_RTC_DERIVES)", TM,
                                 TOK "(END_DERIVES)", BreakSpace(1,2)],
                  term_name = "pprtcderives",
                  fixity = Infix(NONASSOC, 450)}




(* including some backticks `` ensures that this file gets processed with
   unquote*)

val _ = export_theory()
