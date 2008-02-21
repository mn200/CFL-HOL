structure regexpTheory :> regexpTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading regexpTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open listLemmasTheory
  in end;
  val _ = Theory.link_parents
          ("regexp",
          Arbnum.fromString "1203551024",
          Arbnum.fromString "43783")
          [("listLemmas",
           Arbnum.fromString "1203550994",
           Arbnum.fromString "402807")];
  val _ = Theory.incorporate_types "regexp" [("rexp",0), ("symbol",0)];
  val _ = Theory.incorporate_consts "regexp"
     [("regexp6",((T"rexp" "regexp" [] --> T"rexp" "regexp" []))),
      ("regexp5",
       ((T"rexp" "regexp" [] -->
         (T"rexp" "regexp" [] --> T"rexp" "regexp" [])))),
      ("regexp4",
       ((T"rexp" "regexp" [] -->
         (T"rexp" "regexp" [] --> T"rexp" "regexp" [])))),
      ("regexp3",((T"symbol" "regexp" [] --> T"rexp" "regexp" []))),
      ("regexp2",(T"rexp" "regexp" [])),
      ("regexp1",((T"string" "string" [] --> T"symbol" "regexp" []))),
      ("ts2str",((T"symbol" "regexp" [] --> T"string" "string" []))),
      ("regexp0",((T"string" "string" [] --> T"symbol" "regexp" []))),
      ("rexp_case",
       ((alpha -->
         ((T"symbol" "regexp" [] --> alpha) -->
          ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha)) -->
           ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha)) -->
            ((T"rexp" "regexp" [] --> alpha) -->
             (T"rexp" "regexp" [] --> alpha)))))))),
      ("star",
       (((T"list" "list" [alpha] --> bool) -->
         (T"list" "list" [alpha] --> bool)))),
      ("Star",((T"rexp" "regexp" [] --> T"rexp" "regexp" []))),
      ("NTS",((T"string" "string" [] --> T"symbol" "regexp" []))),
      ("symbol_case",
       (((T"string" "string" [] --> alpha) -->
         ((T"string" "string" [] --> alpha) -->
          (T"symbol" "regexp" [] --> alpha))))),
      ("union",
       (((alpha --> bool) --> ((alpha --> bool) --> (alpha --> bool))))),
      ("Union",
       ((T"rexp" "regexp" [] -->
         (T"rexp" "regexp" [] --> T"rexp" "regexp" [])))),
      ("lang",
       ((T"rexp" "regexp" [] -->
         (T"list" "list" [T"string" "string" []] --> bool)))),
      ("starn",
       (((T"list" "list" [alpha] --> bool) -->
         (T"num" "num" [] --> (T"list" "list" [alpha] --> bool))))),
      ("dest_symbol",
       ((T"symbol" "regexp" [] -->
         T"recspace" "ind_type" [T"string" "string" []]))),
      ("rexp_size",((T"rexp" "regexp" [] --> T"num" "num" []))),
      ("symbol_size",((T"symbol" "regexp" [] --> T"num" "num" []))),
      ("EmptyLang",(T"rexp" "regexp" [])),
      ("isTmnlSym",((T"symbol" "regexp" [] --> bool))),
      ("nts2str",((T"symbol" "regexp" [] --> T"string" "string" []))),
      ("conc",
       (((T"list" "list" [alpha] --> bool) -->
         ((T"list" "list" [alpha] --> bool) -->
          (T"list" "list" [alpha] --> bool))))),
      ("Conc",
       ((T"rexp" "regexp" [] -->
         (T"rexp" "regexp" [] --> T"rexp" "regexp" [])))),
      ("Atom",((T"symbol" "regexp" [] --> T"rexp" "regexp" []))),
      ("nonTmnlSym",((T"symbol" "regexp" [] --> T"string" "string" []))),
      ("isNonTmnlSym",((T"symbol" "regexp" [] --> bool))),
      ("dest_rexp",
       ((T"rexp" "regexp" [] -->
         T"recspace" "ind_type" [T"symbol" "regexp" []]))),
      ("TS",((T"string" "string" [] --> T"symbol" "regexp" []))),
      ("sym2Str",((T"symbol" "regexp" [] --> T"string" "string" []))),
      ("mk_symbol",
       ((T"recspace" "ind_type" [T"string" "string" []] -->
         T"symbol" "regexp" []))),
      ("mk_rexp",
       ((T"recspace" "ind_type" [T"symbol" "regexp" []] -->
         T"rexp" "regexp" []))),
      ("starn_tupled",
       ((T"prod" "pair"
          [(T"list" "list" [alpha] --> bool), T"num" "num" []] -->
         (T"list" "list" [alpha] --> bool)))),
      ("tmnlSym",((T"symbol" "regexp" [] --> T"string" "string" [])))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"symbol" "regexp" [] -->
        T"recspace" "ind_type" [T"string" "string" []]) --> bool) -->
      bool)),
   V"rep"
    ((T"symbol" "regexp" [] -->
      T"recspace" "ind_type" [T"string" "string" []])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"string" "string" []] --> bool) -->
      ((T"symbol" "regexp" [] -->
        T"recspace" "ind_type" [T"string" "string" []]) --> bool))),
   V"a0" (T"recspace" "ind_type" [T"string" "string" []]),
   C"!" "bool"
    ((((T"recspace" "ind_type" [T"string" "string" []] --> bool) --> bool)
      --> bool)),
   V"'symbol'" ((T"recspace" "ind_type" [T"string" "string" []] --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type" [T"string" "string" []] --> bool) --> bool)),
   C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"a" (T"string" "string" []),
   C"=" "min"
    ((T"recspace" "ind_type" [T"string" "string" []] -->
      (T"recspace" "ind_type" [T"string" "string" []] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"string" "string" [] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type" [T"string" "string" []]) -->
        T"recspace" "ind_type" [T"string" "string" []])))),
   C"0" "num" (T"num" "num" []), V"n" (T"num" "num" []),
   C"BOTTOM" "ind_type" (T"recspace" "ind_type" [T"string" "string" []]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"a" (T"symbol" "regexp" []),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"mk_symbol" "regexp"
    ((T"recspace" "ind_type" [T"string" "string" []] -->
      T"symbol" "regexp" [])),
   C"dest_symbol" "regexp"
    ((T"symbol" "regexp" [] -->
      T"recspace" "ind_type" [T"string" "string" []])),
   V"r" (T"recspace" "ind_type" [T"string" "string" []]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min"
    (((T"string" "string" [] --> T"symbol" "regexp" []) -->
      ((T"string" "string" [] --> T"symbol" "regexp" []) --> bool))),
   C"regexp0" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"regexp1" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"!" "bool" ((((T"string" "string" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"string" "string" [] --> alpha)),
   V"f1" ((T"string" "string" [] --> alpha)),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"symbol_case" "regexp"
    (((T"string" "string" [] --> alpha) -->
      ((T"string" "string" [] --> alpha) -->
       (T"symbol" "regexp" [] --> alpha)))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"symbol_size" "regexp" ((T"symbol" "regexp" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"string_size" "string" ((T"string" "string" [] --> T"num" "num" [])),
   V"sym" (T"symbol" "regexp" []),
   C"isTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   V"s" (T"string" "string" []),
   C"isNonTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   V"tmnl" (T"string" "string" []),
   C"=" "min"
    ((T"string" "string" [] --> (T"string" "string" [] --> bool))),
   C"tmnlSym" "regexp" ((T"symbol" "regexp" [] --> T"string" "string" [])),
   V"ntmnl" (T"string" "string" []),
   C"nonTmnlSym" "regexp"
    ((T"symbol" "regexp" [] --> T"string" "string" [])),
   C"nts2str" "regexp" ((T"symbol" "regexp" [] --> T"string" "string" [])),
   C"ts2str" "regexp" ((T"symbol" "regexp" [] --> T"string" "string" [])),
   C"sym2Str" "regexp" ((T"symbol" "regexp" [] --> T"string" "string" [])),
   C"?" "bool"
    ((((T"rexp" "regexp" [] -->
        T"recspace" "ind_type" [T"symbol" "regexp" []]) --> bool) -->
      bool)),
   V"rep"
    ((T"rexp" "regexp" [] -->
      T"recspace" "ind_type" [T"symbol" "regexp" []])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"symbol" "regexp" []] --> bool) -->
      ((T"rexp" "regexp" [] -->
        T"recspace" "ind_type" [T"symbol" "regexp" []]) --> bool))),
   V"a0'" (T"recspace" "ind_type" [T"symbol" "regexp" []]),
   C"!" "bool"
    ((((T"recspace" "ind_type" [T"symbol" "regexp" []] --> bool) --> bool)
      --> bool)),
   V"'rexp'" ((T"recspace" "ind_type" [T"symbol" "regexp" []] --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type" [T"symbol" "regexp" []] --> bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type" [T"symbol" "regexp" []] -->
      (T"recspace" "ind_type" [T"symbol" "regexp" []] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"symbol" "regexp" [] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type" [T"symbol" "regexp" []]) -->
        T"recspace" "ind_type" [T"symbol" "regexp" []])))),
   C"@" "min"
    (((T"symbol" "regexp" [] --> bool) --> T"symbol" "regexp" [])),
   V"v" (T"symbol" "regexp" []), C"T" "bool" (bool),
   C"BOTTOM" "ind_type" (T"recspace" "ind_type" [T"symbol" "regexp" []]),
   C"?" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   C"?" "bool"
    (((T"recspace" "ind_type" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"a0" (T"recspace" "ind_type" [T"symbol" "regexp" []]),
   V"a1" (T"recspace" "ind_type" [T"symbol" "regexp" []]),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type" [T"symbol" "regexp" []] -->
      ((T"num" "num" [] --> T"recspace" "ind_type" [T"symbol" "regexp" []])
       -->
       (T"num" "num" [] -->
        T"recspace" "ind_type" [T"symbol" "regexp" []])))),
   V"a" (T"recspace" "ind_type" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"rexp" "regexp" [] --> bool) --> bool)),
   V"a" (T"rexp" "regexp" []),
   C"=" "min" ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> bool))),
   C"mk_rexp" "regexp"
    ((T"recspace" "ind_type" [T"symbol" "regexp" []] -->
      T"rexp" "regexp" [])),
   C"dest_rexp" "regexp"
    ((T"rexp" "regexp" [] -->
      T"recspace" "ind_type" [T"symbol" "regexp" []])),
   V"r" (T"recspace" "ind_type" [T"symbol" "regexp" []]),
   C"regexp2" "regexp" (T"rexp" "regexp" []),
   C"=" "min"
    (((T"symbol" "regexp" [] --> T"rexp" "regexp" []) -->
      ((T"symbol" "regexp" [] --> T"rexp" "regexp" []) --> bool))),
   C"regexp3" "regexp" ((T"symbol" "regexp" [] --> T"rexp" "regexp" [])),
   C"=" "min"
    (((T"rexp" "regexp" [] -->
       (T"rexp" "regexp" [] --> T"rexp" "regexp" [])) -->
      ((T"rexp" "regexp" [] -->
        (T"rexp" "regexp" [] --> T"rexp" "regexp" [])) --> bool))),
   C"regexp4" "regexp"
    ((T"rexp" "regexp" [] -->
      (T"rexp" "regexp" [] --> T"rexp" "regexp" []))),
   V"a0" (T"rexp" "regexp" []), V"a1" (T"rexp" "regexp" []),
   C"regexp5" "regexp"
    ((T"rexp" "regexp" [] -->
      (T"rexp" "regexp" [] --> T"rexp" "regexp" []))),
   C"=" "min"
    (((T"rexp" "regexp" [] --> T"rexp" "regexp" []) -->
      ((T"rexp" "regexp" [] --> T"rexp" "regexp" []) --> bool))),
   C"regexp6" "regexp" ((T"rexp" "regexp" [] --> T"rexp" "regexp" [])),
   C"EmptyLang" "regexp" (T"rexp" "regexp" []),
   C"Atom" "regexp" ((T"symbol" "regexp" [] --> T"rexp" "regexp" [])),
   C"Union" "regexp"
    ((T"rexp" "regexp" [] -->
      (T"rexp" "regexp" [] --> T"rexp" "regexp" []))),
   C"Conc" "regexp"
    ((T"rexp" "regexp" [] -->
      (T"rexp" "regexp" [] --> T"rexp" "regexp" []))),
   C"Star" "regexp" ((T"rexp" "regexp" [] --> T"rexp" "regexp" [])),
   C"!" "bool" (((alpha --> bool) --> bool)), V"v" (alpha),
   C"!" "bool" ((((T"symbol" "regexp" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"symbol" "regexp" [] --> alpha)),
   C"!" "bool"
    ((((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha)) --> bool)
      --> bool)),
   V"f1" ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha))),
   V"f2" ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha))),
   C"!" "bool" ((((T"rexp" "regexp" [] --> alpha) --> bool) --> bool)),
   V"f3" ((T"rexp" "regexp" [] --> alpha)),
   C"rexp_case" "regexp"
    ((alpha -->
      ((T"symbol" "regexp" [] --> alpha) -->
       ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha)) -->
        ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha)) -->
         ((T"rexp" "regexp" [] --> alpha) -->
          (T"rexp" "regexp" [] --> alpha))))))),
   C"rexp_size" "regexp" ((T"rexp" "regexp" [] --> T"num" "num" [])),
   C"!" "bool" ((((T"list" "list" [alpha] --> bool) --> bool) --> bool)),
   V"as" ((T"list" "list" [alpha] --> bool)),
   V"bs" ((T"list" "list" [alpha] --> bool)),
   C"=" "min"
    (((T"list" "list" [alpha] --> bool) -->
      ((T"list" "list" [alpha] --> bool) --> bool))),
   C"conc" "regexp"
    (((T"list" "list" [alpha] --> bool) -->
      ((T"list" "list" [alpha] --> bool) -->
       (T"list" "list" [alpha] --> bool)))),
   C"GSPEC" "pred_set"
    (((T"list" "list" [alpha] -->
       T"prod" "pair" [T"list" "list" [alpha], bool]) -->
      (T"list" "list" [alpha] --> bool))), V"s" (T"list" "list" [alpha]),
   C"," "pair"
    ((T"list" "list" [alpha] -->
      (bool --> T"prod" "pair" [T"list" "list" [alpha], bool]))),
   C"?" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"u" (T"list" "list" [alpha]), V"v" (T"list" "list" [alpha]),
   C"IN" "bool"
    ((T"list" "list" [alpha] -->
      ((T"list" "list" [alpha] --> bool) --> bool))),
   C"=" "min"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"APPEND" "list"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"as" ((alpha --> bool)), V"bs" ((alpha --> bool)),
   C"=" "min" (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"union" "regexp"
    (((alpha --> bool) --> ((alpha --> bool) --> (alpha --> bool)))),
   C"GSPEC" "pred_set"
    (((alpha --> T"prod" "pair" [alpha, bool]) --> (alpha --> bool))),
   V"s" (alpha),
   C"," "pair" ((alpha --> (bool --> T"prod" "pair" [alpha, bool]))),
   C"IN" "bool" ((alpha --> ((alpha --> bool) --> bool))),
   C"=" "min"
    (((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
       --> (T"list" "list" [alpha] --> bool)) -->
      ((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
        --> (T"list" "list" [alpha] --> bool)) --> bool))),
   C"starn_tupled" "regexp"
    ((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
      --> (T"list" "list" [alpha] --> bool))),
   C"WFREC" "relation"
    (((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
       -->
       (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
        --> bool)) -->
      (((T"prod" "pair"
          [(T"list" "list" [alpha] --> bool), T"num" "num" []] -->
         (T"list" "list" [alpha] --> bool)) -->
        (T"prod" "pair"
          [(T"list" "list" [alpha] --> bool), T"num" "num" []] -->
         (T"list" "list" [alpha] --> bool))) -->
       (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
        --> (T"list" "list" [alpha] --> bool))))),
   C"@" "min"
    ((((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
        -->
        (T"prod" "pair"
          [(T"list" "list" [alpha] --> bool), T"num" "num" []] --> bool))
       --> bool) -->
      (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
       -->
       (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
        --> bool)))),
   V"R"
    ((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
      -->
      (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
       -->
       (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
        --> bool)) --> bool)),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"v2" (T"num" "num" []), V"l" ((T"list" "list" [alpha] --> bool)),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   C"," "pair"
    (((T"list" "list" [alpha] --> bool) -->
      (T"num" "num" [] -->
       T"prod" "pair"
        [(T"list" "list" [alpha] --> bool), T"num" "num" []]))),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   V"starn_tupled"
    ((T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
      --> (T"list" "list" [alpha] --> bool))),
   V"a"
    (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]),
   C"pair_case" "pair"
    ((((T"list" "list" [alpha] --> bool) -->
       (T"num" "num" [] --> (T"list" "list" [alpha] --> bool))) -->
      (T"prod" "pair" [(T"list" "list" [alpha] --> bool), T"num" "num" []]
       --> (T"list" "list" [alpha] --> bool)))), V"v1" (T"num" "num" []),
   C"num_case" "arithmetic"
    (((T"list" "list" [alpha] --> bool) -->
      ((T"num" "num" [] --> (T"list" "list" [alpha] --> bool)) -->
       (T"num" "num" [] --> (T"list" "list" [alpha] --> bool))))),
   C"I" "combin"
    (((T"list" "list" [alpha] --> bool) -->
      (T"list" "list" [alpha] --> bool))),
   C"INSERT" "pred_set"
    ((T"list" "list" [alpha] -->
      ((T"list" "list" [alpha] --> bool) -->
       (T"list" "list" [alpha] --> bool)))),
   C"NIL" "list" (T"list" "list" [alpha]),
   C"EMPTY" "pred_set" ((T"list" "list" [alpha] --> bool)),
   V"v3" (T"num" "num" []), V"x" ((T"list" "list" [alpha] --> bool)),
   V"x1" (T"num" "num" []),
   C"starn" "regexp"
    (((T"list" "list" [alpha] --> bool) -->
      (T"num" "num" [] --> (T"list" "list" [alpha] --> bool)))),
   C"=" "min"
    ((((T"list" "list" [alpha] --> bool) -->
       (T"list" "list" [alpha] --> bool)) -->
      (((T"list" "list" [alpha] --> bool) -->
        (T"list" "list" [alpha] --> bool)) --> bool))),
   C"star" "regexp"
    (((T"list" "list" [alpha] --> bool) -->
      (T"list" "list" [alpha] --> bool))),
   V"A" ((T"list" "list" [alpha] --> bool)),
   V"a0" (T"list" "list" [alpha]),
   V"star'" ((T"list" "list" [alpha] --> bool)),
   V"s1" (T"list" "list" [alpha]), V"s2" (T"list" "list" [alpha]),
   C"=" "min"
    (((T"list" "list" [T"string" "string" []] --> bool) -->
      ((T"list" "list" [T"string" "string" []] --> bool) --> bool))),
   C"lang" "regexp"
    ((T"rexp" "regexp" [] -->
      (T"list" "list" [T"string" "string" []] --> bool))),
   C"EMPTY" "pred_set" ((T"list" "list" [T"string" "string" []] --> bool)),
   V"tmnl" (T"symbol" "regexp" []),
   C"INSERT" "pred_set"
    ((T"list" "list" [T"string" "string" []] -->
      ((T"list" "list" [T"string" "string" []] --> bool) -->
       (T"list" "list" [T"string" "string" []] --> bool)))),
   C"CONS" "list"
    ((T"string" "string" [] -->
      (T"list" "list" [T"string" "string" []] -->
       T"list" "list" [T"string" "string" []]))),
   C"NIL" "list" (T"list" "list" [T"string" "string" []]),
   V"r" (T"rexp" "regexp" []), V"s" (T"rexp" "regexp" []),
   C"UNION" "pred_set"
    (((T"list" "list" [T"string" "string" []] --> bool) -->
      ((T"list" "list" [T"string" "string" []] --> bool) -->
       (T"list" "list" [T"string" "string" []] --> bool)))),
   C"conc" "regexp"
    (((T"list" "list" [T"string" "string" []] --> bool) -->
      ((T"list" "list" [T"string" "string" []] --> bool) -->
       (T"list" "list" [T"string" "string" []] --> bool)))),
   C"star" "regexp"
    (((T"list" "list" [T"string" "string" []] --> bool) -->
      (T"list" "list" [T"string" "string" []] --> bool))),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"symbol"
    (((T"string" "string" [] --> T"symbol" "regexp" []) -->
      ((T"string" "string" [] --> T"symbol" "regexp" []) --> bool))),
   V"a'" (T"string" "string" []), C"~" "bool" ((bool --> bool)),
   V"M" (T"symbol" "regexp" []), V"M'" (T"symbol" "regexp" []),
   V"f'" ((T"string" "string" [] --> alpha)),
   V"f1'" ((T"string" "string" [] --> alpha)),
   V"s" (T"symbol" "regexp" []), V"f0" ((T"string" "string" [] --> alpha)),
   C"?" "bool" ((((T"symbol" "regexp" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"symbol" "regexp" [] --> alpha)),
   C"!" "bool" ((((T"symbol" "regexp" [] --> bool) --> bool) --> bool)),
   V"P" ((T"symbol" "regexp" [] --> bool)), V"nt" (T"string" "string" []),
   C"F" "bool" (bool), V"ts" (T"string" "string" []),
   V"e" (T"symbol" "regexp" []), V"n" (T"string" "string" []),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"v" (T"list" "list" [T"symbol" "regexp" []]),
   C"EVERY" "list"
    (((T"symbol" "regexp" [] --> bool) -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   V"n" (T"symbol" "regexp" []),
   C"?" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"s1" (T"list" "list" [T"symbol" "regexp" []]),
   V"s2" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"APPEND" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   C"MEM" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   V"s" (T"list" "list" [T"symbol" "regexp" []]),
   V"l1" (T"list" "list" [T"symbol" "regexp" []]),
   V"l2" (T"list" "list" [T"symbol" "regexp" []]),
   V"rexp"
    ((T"rexp" "regexp" [] -->
      ((T"symbol" "regexp" [] --> T"rexp" "regexp" []) -->
       ((T"rexp" "regexp" [] -->
         (T"rexp" "regexp" [] --> T"rexp" "regexp" [])) -->
        ((T"rexp" "regexp" [] -->
          (T"rexp" "regexp" [] --> T"rexp" "regexp" [])) -->
         ((T"rexp" "regexp" [] --> T"rexp" "regexp" []) --> bool)))))),
   V"a'" (T"symbol" "regexp" []), V"a0'" (T"rexp" "regexp" []),
   V"a1'" (T"rexp" "regexp" []), V"a'" (T"rexp" "regexp" []),
   V"M" (T"rexp" "regexp" []), V"M'" (T"rexp" "regexp" []), V"v'" (alpha),
   V"f'" ((T"symbol" "regexp" [] --> alpha)),
   V"f1'" ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha))),
   V"f2'" ((T"rexp" "regexp" [] --> (T"rexp" "regexp" [] --> alpha))),
   V"f3'" ((T"rexp" "regexp" [] --> alpha)),
   C"?" "bool" (((T"rexp" "regexp" [] --> bool) --> bool)),
   V"r0" (T"rexp" "regexp" []), V"f0" (alpha),
   V"f1" ((T"symbol" "regexp" [] --> alpha)),
   C"!" "bool"
    ((((T"rexp" "regexp" [] -->
        (T"rexp" "regexp" [] --> (alpha --> (alpha --> alpha)))) --> bool)
      --> bool)),
   V"f2"
    ((T"rexp" "regexp" [] -->
      (T"rexp" "regexp" [] --> (alpha --> (alpha --> alpha))))),
   V"f3"
    ((T"rexp" "regexp" [] -->
      (T"rexp" "regexp" [] --> (alpha --> (alpha --> alpha))))),
   C"!" "bool"
    ((((T"rexp" "regexp" [] --> (alpha --> alpha)) --> bool) --> bool)),
   V"f4" ((T"rexp" "regexp" [] --> (alpha --> alpha))),
   C"?" "bool" ((((T"rexp" "regexp" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"rexp" "regexp" [] --> alpha)),
   C"!" "bool" ((((T"rexp" "regexp" [] --> bool) --> bool) --> bool)),
   V"P" ((T"rexp" "regexp" [] --> bool)),
   C"!" "bool"
    (((((T"list" "list" [alpha] --> bool) --> (T"num" "num" [] --> bool))
       --> bool) --> bool)),
   V"P"
    (((T"list" "list" [alpha] --> bool) --> (T"num" "num" [] --> bool))),
   V"v" ((T"list" "list" [alpha] --> bool))]
  val DT = Thm.disk_thm share_table
  in
  val symbol_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 ((%8 (%9 (\%10.
       ((%11 $1) ((\%10. (((%12 %13) $0) (\%14. %15))) $0))))) (%9 (\%10.
       ((%11 $1) ((\%10. (((%12 (%16 %13)) $0) (\%14. %15))) $0)))))) ($1
       $0))))) ($0 $1)))))) $0)))`)
  val symbol_repfns =
    DT(["DISK_THM"], [],
       `((%17 (%18 (\%19. ((%20 (%21 (%22 $0))) $0)))) (%7 (\%23. ((%24
       ((\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 ((%8 (%9 (\%10. ((%11 $1)
       ((\%10. (((%12 %13) $0) (\%14. %15))) $0))))) (%9 (\%10. ((%11 $1)
       ((\%10. (((%12 (%16 %13)) $0) (\%14. %15))) $0)))))) ($1 $0))))) ($0
       $1))))) $0)) ((%11 (%22 (%21 $0))) $0)))))`)
  val regexp0_def =
    DT([], [],
       `((%25 %26) (\%10. (%21 ((\%10. (((%12 %13) $0) (\%14. %15)))
       $0))))`)
  val regexp1_def =
    DT([], [],
       `((%25 %27) (\%10. (%21 ((\%10. (((%12 (%16 %13)) $0) (\%14. %15)))
       $0))))`)
  val TS = DT([], [], `((%25 %28) %26)`)
  val NTS = DT([], [], `((%25 %29) %27)`)
  val symbol_case_def =
    DT(["DISK_THM"], [],
       `((%17 (%30 (\%31. (%30 (\%32. (%33 (\%10. ((%34 (((%35 $2) $1) (%28
       $0))) ($2 $0))))))))) (%30 (\%31. (%30 (\%32. (%33 (\%10. ((%34
       (((%35 $2) $1) (%29 $0))) ($1 $0)))))))))`)
  val symbol_size_def =
    DT(["DISK_THM"], [],
       `((%17 (%33 (\%10. ((%36 (%37 (%28 $0))) ((%38 (%39 (%40 %41))) (%42
       $0)))))) (%33 (\%10. ((%36 (%37 (%29 $0))) ((%38 (%39 (%40 %41)))
       (%42 $0))))))`)
  val isTmnlSym_def =
    DT([], [],
       `(%18 (\%43. ((%24 (%44 $0)) (%9 (\%45. ((%20 $1) (%28 $0)))))))`)
  val isNonTmnlSym_def =
    DT([], [],
       `(%18 (\%43. ((%24 (%46 $0)) (%9 (\%45. ((%20 $1) (%29 $0)))))))`)
  val tmnlSym_def =
    DT(["DISK_THM"], [], `(%33 (\%47. ((%48 (%49 (%28 $0))) $0)))`)
  val nonTmnlSym_def =
    DT(["DISK_THM"], [], `(%33 (\%50. ((%48 (%51 (%29 $0))) $0)))`)
  val nts2str_def =
    DT(["DISK_THM"], [], `(%33 (\%45. ((%48 (%52 (%29 $0))) $0)))`)
  val ts2str_def =
    DT(["DISK_THM"], [], `(%33 (\%45. ((%48 (%53 (%28 $0))) $0)))`)
  val sym2Str_def =
    DT(["DISK_THM"], [],
       `((%17 (%33 (\%45. ((%48 (%54 (%28 $0))) $0)))) (%33 (\%45. ((%48
       (%54 (%29 $0))) $0))))`)
  val rexp_TY_DEF =
    DT(["DISK_THM"], [],
       `(%55 (\%56. ((%57 (\%58. (%59 (\%60. ((%6 (%61 (\%58. ((%6 ((%8
       ((%62 $0) (((%63 %13) (%64 (\%65. %66))) (\%14. %67)))) ((%8 (%68
       (\%19. ((%62 $1) ((\%19. (((%63 (%16 %13)) $0) (\%14. %67))) $0)))))
       ((%8 (%69 (\%70. (%69 (\%71. ((%17 ((%62 $2) (((\%70. (\%71. (((%63
       (%16 (%16 %13))) (%64 (\%65. %66))) ((%72 $1) ((%72 $0) (\%14.
       %67)))))) $1) $0))) ((%17 ($3 $1)) ($3 $0)))))))) ((%8 (%69 (\%70.
       (%69 (\%71. ((%17 ((%62 $2) (((\%70. (\%71. (((%63 (%16 (%16 (%16
       %13)))) (%64 (\%65. %66))) ((%72 $1) ((%72 $0) (\%14. %67)))))) $1)
       $0))) ((%17 ($3 $1)) ($3 $0)))))))) (%69 (\%73. ((%17 ((%62 $1)
       ((\%73. (((%63 (%16 (%16 (%16 (%16 %13))))) (%64 (\%65. %66))) ((%72
       $0) (\%14. %67)))) $0))) ($2 $0))))))))) ($1 $0))))) ($0 $1))))))
       $0)))`)
  val rexp_repfns =
    DT(["DISK_THM"], [],
       `((%17 (%74 (\%75. ((%76 (%77 (%78 $0))) $0)))) (%61 (\%79. ((%24
       ((\%58. (%59 (\%60. ((%6 (%61 (\%58. ((%6 ((%8 ((%62 $0) (((%63 %13)
       (%64 (\%65. %66))) (\%14. %67)))) ((%8 (%68 (\%19. ((%62 $1) ((\%19.
       (((%63 (%16 %13)) $0) (\%14. %67))) $0))))) ((%8 (%69 (\%70. (%69
       (\%71. ((%17 ((%62 $2) (((\%70. (\%71. (((%63 (%16 (%16 %13))) (%64
       (\%65. %66))) ((%72 $1) ((%72 $0) (\%14. %67)))))) $1) $0))) ((%17
       ($3 $1)) ($3 $0)))))))) ((%8 (%69 (\%70. (%69 (\%71. ((%17 ((%62 $2)
       (((\%70. (\%71. (((%63 (%16 (%16 (%16 %13)))) (%64 (\%65. %66)))
       ((%72 $1) ((%72 $0) (\%14. %67)))))) $1) $0))) ((%17 ($3 $1)) ($3
       $0)))))))) (%69 (\%73. ((%17 ((%62 $1) ((\%73. (((%63 (%16 (%16 (%16
       (%16 %13))))) (%64 (\%65. %66))) ((%72 $0) (\%14. %67)))) $0))) ($2
       $0))))))))) ($1 $0))))) ($0 $1))))) $0)) ((%62 (%78 (%77 $0)))
       $0)))))`)
  val regexp2_def =
    DT([], [],
       `((%76 %80) (%77 (((%63 %13) (%64 (\%65. %66))) (\%14. %67))))`)
  val regexp3_def =
    DT([], [],
       `((%81 %82) (\%19. (%77 ((\%19. (((%63 (%16 %13)) $0) (\%14. %67)))
       $0))))`)
  val regexp4_def =
    DT([], [],
       `((%83 %84) (\%85. (\%86. (%77 (((\%70. (\%71. (((%63 (%16 (%16
       %13))) (%64 (\%65. %66))) ((%72 $1) ((%72 $0) (\%14. %67)))))) (%78
       $1)) (%78 $0))))))`)
  val regexp5_def =
    DT([], [],
       `((%83 %87) (\%85. (\%86. (%77 (((\%70. (\%71. (((%63 (%16 (%16 (%16
       %13)))) (%64 (\%65. %66))) ((%72 $1) ((%72 $0) (\%14. %67)))))) (%78
       $1)) (%78 $0))))))`)
  val regexp6_def =
    DT([], [],
       `((%88 %89) (\%75. (%77 ((\%73. (((%63 (%16 (%16 (%16 (%16 %13)))))
       (%64 (\%65. %66))) ((%72 $0) (\%14. %67)))) (%78 $0)))))`)
  val EmptyLang = DT([], [], `((%76 %90) %80)`)
  val Atom = DT([], [], `((%81 %91) %82)`)
  val Union = DT([], [], `((%83 %92) %84)`)
  val Conc = DT([], [], `((%83 %93) %87)`)
  val Star = DT([], [], `((%88 %94) %89)`)
  val rexp_case_def =
    DT(["DISK_THM"], [],
       `((%17 (%95 (\%96. (%97 (\%98. (%99 (\%100. (%99 (\%101. (%102
       (\%103. ((%34 ((((((%104 $4) $3) $2) $1) $0) %90)) $4))))))))))))
       ((%17 (%95 (\%96. (%97 (\%98. (%99 (\%100. (%99 (\%101. (%102
       (\%103. (%18 (\%19. ((%34 ((((((%104 $5) $4) $3) $2) $1) (%91 $0)))
       ($4 $0))))))))))))))) ((%17 (%95 (\%96. (%97 (\%98. (%99 (\%100.
       (%99 (\%101. (%102 (\%103. (%74 (\%85. (%74 (\%86. ((%34 ((((((%104
       $6) $5) $4) $3) $2) ((%92 $1) $0))) (($4 $1) $0)))))))))))))))))
       ((%17 (%95 (\%96. (%97 (\%98. (%99 (\%100. (%99 (\%101. (%102
       (\%103. (%74 (\%85. (%74 (\%86. ((%34 ((((((%104 $6) $5) $4) $3) $2)
       ((%93 $1) $0))) (($3 $1) $0))))))))))))))))) (%95 (\%96. (%97 (\%98.
       (%99 (\%100. (%99 (\%101. (%102 (\%103. (%74 (\%75. ((%34 ((((((%104
       $5) $4) $3) $2) $1) (%94 $0))) ($1 $0))))))))))))))))))`)
  val rexp_size_def =
    DT(["DISK_THM"], [],
       `((%17 ((%36 (%105 %90)) %13)) ((%17 (%18 (\%19. ((%36 (%105 (%91
       $0))) ((%38 (%39 (%40 %41))) (%37 $0)))))) ((%17 (%74 (\%85. (%74
       (\%86. ((%36 (%105 ((%92 $1) $0))) ((%38 (%39 (%40 %41))) ((%38
       (%105 $1)) (%105 $0))))))))) ((%17 (%74 (\%85. (%74 (\%86. ((%36
       (%105 ((%93 $1) $0))) ((%38 (%39 (%40 %41))) ((%38 (%105 $1)) (%105
       $0))))))))) (%74 (\%75. ((%36 (%105 (%94 $0))) ((%38 (%39 (%40
       %41))) (%105 $0)))))))))`)
  val conc_def =
    DT([], [],
       `(%106 (\%107. (%106 (\%108. ((%109 ((%110 $1) $0)) (%111 (\%112.
       ((%113 $0) (%114 (\%115. (%114 (\%116. ((%17 ((%117 $1) $4)) ((%17
       ((%117 $0) $3)) ((%118 $2) ((%119 $1) $0))))))))))))))))`)
  val union_def =
    DT([], [],
       `(%120 (\%121. (%120 (\%122. ((%123 ((%124 $1) $0)) (%125 (\%126.
       ((%127 $0) ((%8 ((%128 $0) $2)) ((%128 $0) $1))))))))))`)
  val starn_tupled_primitive_def =
    DT([], [],
       `((%129 %130) ((%131 (%132 (\%133. ((%17 (%134 $0)) (%135 (\%136.
       (%106 (\%137. (%138 (\%115. (%138 (\%112. (%138 (\%116. ((%6 ((%17
       ((%117 $2) $3)) ((%118 $1) ((%119 $2) $0)))) (($5 ((%139 $3) ((%140
       (%16 $4)) (%39 (%40 %41))))) ((%139 $3) (%16 $4))))))))))))))))))
       (\%141. (\%142. ((%143 (\%137. (\%144. (((%145 (%146 ((%147 %148)
       %149))) (\%150. (%146 (%111 (\%112. ((%113 $0) (%114 (\%115. (%114
       (\%116. ((%17 ((%117 $1) $5)) ((%17 ((%117 $0) ($7 ((%139 $5) ((%140
       (%16 $3)) (%39 (%40 %41))))))) ((%118 $2) ((%119 $1)
       $0)))))))))))))) $0)))) $0)))))`)
  val starn_curried_def =
    DT([], [],
       `(%106 (\%151. (%135 (\%152. ((%109 ((%153 $1) $0)) (%130 ((%139 $1)
       $0)))))))`)
  val star =
    DT([], [],
       `((%154 %155) (\%156. (\%157. (%106 (\%158. ((%6 (%138 (\%157. ((%6
       ((%8 ((%118 $0) %148)) ((%8 ((%117 $0) $3)) (%114 (\%159. (%114
       (\%160. ((%17 ((%118 $2) ((%119 $1) $0))) ((%17 ((%117 $1) $5))
       ((%117 $0) $5)))))))))) ($1 $0))))) ($0 $1)))))))`)
  val lang_def =
    DT(["DISK_THM"], [],
       `((%17 ((%161 (%162 %90)) %163)) ((%17 (%18 (\%164. ((%161 (%162
       (%91 $0))) ((%165 ((%166 (%54 $0)) %167)) %163))))) ((%17 (%74
       (\%168. (%74 (\%169. ((%161 (%162 ((%92 $1) $0))) ((%170 (%162 $1))
       (%162 $0)))))))) ((%17 (%74 (\%168. (%74 (\%169. ((%161 (%162 ((%93
       $1) $0))) ((%171 (%162 $1)) (%162 $0)))))))) (%74 (\%168. ((%161
       (%162 (%94 $0))) (%172 (%162 $0)))))))))`)
  val datatype_symbol = DT(["DISK_THM"], [], `(%173 ((%174 %28) %29))`)
  val symbol_11 =
    DT(["DISK_THM"], [],
       `((%17 (%33 (\%10. (%33 (\%175. ((%24 ((%20 (%28 $1)) (%28 $0)))
       ((%48 $1) $0))))))) (%33 (\%10. (%33 (\%175. ((%24 ((%20 (%29 $1))
       (%29 $0))) ((%48 $1) $0)))))))`)
  val symbol_distinct =
    DT(["DISK_THM"], [],
       `(%33 (\%175. (%33 (\%10. (%176 ((%20 (%28 $0)) (%29 $1)))))))`)
  val symbol_case_cong =
    DT(["DISK_THM"], [],
       `(%18 (\%177. (%18 (\%178. (%30 (\%31. (%30 (\%32. ((%6 ((%17 ((%20
       $3) $2)) ((%17 (%33 (\%10. ((%6 ((%20 $3) (%28 $0))) ((%34 ($2 $0))
       (%179 $0)))))) (%33 (\%10. ((%6 ((%20 $3) (%29 $0))) ((%34 ($1 $0))
       (%180 $0)))))))) ((%34 (((%35 $1) $0) $3)) (((%35 %179) %180)
       $2)))))))))))`)
  val symbol_nchotomy =
    DT(["DISK_THM"], [],
       `(%18 (\%181. ((%8 (%9 (\%45. ((%20 $1) (%28 $0))))) (%9 (\%45.
       ((%20 $1) (%29 $0)))))))`)
  val symbol_Axiom =
    DT(["DISK_THM"], [],
       `(%30 (\%182. (%30 (\%32. (%183 (\%184. ((%17 (%33 (\%10. ((%34 ($1
       (%28 $0))) ($3 $0))))) (%33 (\%10. ((%34 ($1 (%29 $0))) ($2
       $0)))))))))))`)
  val symbol_induction =
    DT(["DISK_THM"], [],
       `(%185 (\%186. ((%6 ((%17 (%33 (\%45. ($1 (%28 $0))))) (%33 (\%45.
       ($1 (%29 $0)))))) (%18 (\%181. ($1 $0))))))`)
  val isTmnlSymML =
    DT(["DISK_THM"], [],
       `((%17 ((%24 (%44 (%29 %187))) %188)) ((%24 (%44 (%28 %189)))
       %66))`)
  val isNonTmnlSymML =
    DT(["DISK_THM"], [],
       `((%17 ((%24 (%46 (%29 %187))) %66)) ((%24 (%46 (%28 %45))) %188))`)
  val sym_r1a = DT(["DISK_THM"], [], `((%6 (%44 %190)) (%176 (%46 %190)))`)
  val sym_r1b =
    DT(["DISK_THM"], [], `((%24 (%176 (%44 %190))) (%46 %190))`)
  val sym_r2 =
    DT(["DISK_THM"], [],
       `((%6 (%44 %190)) (%176 (%9 (\%191. ((%20 %190) (%29 $0))))))`)
  val sym_r3 =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 ((%194 %44) $0)) (%176 (%68 (\%195. (%196
       (\%197. (%196 (\%198. ((%17 ((%199 $3) ((%200 ((%200 $1) ((%201 $2)
       %202))) $0))) (%46 $2))))))))))))`)
  val sym_r3b =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 ((%194 %46) $0)) (%176 (%68 (\%195. (%196
       (\%197. (%196 (\%198. ((%17 ((%199 $3) ((%200 ((%200 $1) ((%201 $2)
       %202))) $0))) (%44 $2))))))))))))`)
  val sym_r4 =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 ((%194 %44) $0)) (%176 (%68 (\%195. ((%17 ((%203
       $0) $1)) (%176 (%44 $0)))))))))`)
  val sym_r4b =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 (%176 ((%194 %44) $0))) (%68 (\%195. ((%17
       ((%203 $0) $1)) (%46 $0)))))))`)
  val sym_r5 =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 (%176 (%68 (\%195. (%196 (\%197. (%196 (\%198.
       ((%17 ((%199 $3) ((%200 ((%200 $1) ((%201 $2) %202))) $0))) (%46
       $2)))))))))) ((%194 %44) $0))))`)
  val sym_r6 =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%24 ((%194 %44) $0)) (%176 (%68 (\%195. (%196
       (\%197. (%196 (\%198. ((%17 ((%199 $3) ((%200 ((%200 $1) ((%201 $2)
       %202))) $0))) (%46 $2))))))))))))`)
  val sym_r7 =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 (%176 ((%194 %44) $0))) (%68 (\%195. (%196
       (\%197. (%196 (\%198. ((%17 ((%199 $3) ((%200 ((%200 $1) ((%201 $2)
       %202))) $0))) (%46 $2)))))))))))`)
  val sym_r7b =
    DT(["DISK_THM"], [],
       `(%192 (\%193. ((%6 (%176 ((%194 %46) $0))) (%68 (\%195. (%196
       (\%197. (%196 (\%198. ((%17 ((%199 $3) ((%200 ((%200 $1) ((%201 $2)
       %202))) $0))) (%44 $2)))))))))))`)
  val rightnt =
    DT(["DISK_THM"], [],
       `(%192 (\%204. ((%6 (%176 ((%194 %44) $0))) (%196 (\%205. (%9
       (\%191. (%196 (\%206. ((%17 ((%199 $3) ((%200 ((%200 $2) ((%201 (%29
       $1)) %202))) $0))) ((%194 %44) $0)))))))))))`)
  val datatype_rexp =
    DT(["DISK_THM"], [], `(%173 (((((%207 %90) %91) %92) %93) %94))`)
  val rexp_11 =
    DT(["DISK_THM"], [],
       `((%17 (%18 (\%19. (%18 (\%208. ((%24 ((%76 (%91 $1)) (%91 $0)))
       ((%20 $1) $0))))))) ((%17 (%74 (\%85. (%74 (\%86. (%74 (\%209. (%74
       (\%210. ((%24 ((%76 ((%92 $3) $2)) ((%92 $1) $0))) ((%17 ((%76 $3)
       $1)) ((%76 $2) $0)))))))))))) ((%17 (%74 (\%85. (%74 (\%86. (%74
       (\%209. (%74 (\%210. ((%24 ((%76 ((%93 $3) $2)) ((%93 $1) $0)))
       ((%17 ((%76 $3) $1)) ((%76 $2) $0)))))))))))) (%74 (\%75. (%74
       (\%211. ((%24 ((%76 (%94 $1)) (%94 $0))) ((%76 $1) $0)))))))))`)
  val rexp_distinct =
    DT(["DISK_THM"], [],
       `((%17 (%18 (\%19. (%176 ((%76 %90) (%91 $0)))))) ((%17 (%74 (\%86.
       (%74 (\%85. (%176 ((%76 %90) ((%92 $0) $1)))))))) ((%17 (%74 (\%86.
       (%74 (\%85. (%176 ((%76 %90) ((%93 $0) $1)))))))) ((%17 (%74 (\%75.
       (%176 ((%76 %90) (%94 $0)))))) ((%17 (%74 (\%86. (%74 (\%85. (%18
       (\%19. (%176 ((%76 (%91 $0)) ((%92 $1) $2)))))))))) ((%17 (%74
       (\%86. (%74 (\%85. (%18 (\%19. (%176 ((%76 (%91 $0)) ((%93 $1)
       $2)))))))))) ((%17 (%74 (\%211. (%18 (\%19. (%176 ((%76 (%91 $0))
       (%94 $1)))))))) ((%17 (%74 (\%210. (%74 (\%86. (%74 (\%209. (%74
       (\%85. (%176 ((%76 ((%92 $0) $2)) ((%93 $1) $3)))))))))))) ((%17
       (%74 (\%86. (%74 (\%85. (%74 (\%75. (%176 ((%76 ((%92 $1) $2)) (%94
       $0)))))))))) (%74 (\%86. (%74 (\%85. (%74 (\%75. (%176 ((%76 ((%93
       $1) $2)) (%94 $0))))))))))))))))))`)
  val rexp_case_cong =
    DT(["DISK_THM"], [],
       `(%74 (\%212. (%74 (\%213. (%95 (\%96. (%97 (\%98. (%99 (\%100. (%99
       (\%101. (%102 (\%103. ((%6 ((%17 ((%76 $6) $5)) ((%17 ((%6 ((%76 $5)
       %90)) ((%34 $4) %214))) ((%17 (%18 (\%19. ((%6 ((%76 $6) (%91 $0)))
       ((%34 ($4 $0)) (%215 $0)))))) ((%17 (%74 (\%85. (%74 (\%86. ((%6
       ((%76 $7) ((%92 $1) $0))) ((%34 (($4 $1) $0)) ((%216 $1) $0))))))))
       ((%17 (%74 (\%85. (%74 (\%86. ((%6 ((%76 $7) ((%93 $1) $0))) ((%34
       (($3 $1) $0)) ((%217 $1) $0)))))))) (%74 (\%75. ((%6 ((%76 $6) (%94
       $0))) ((%34 ($1 $0)) (%218 $0))))))))))) ((%34 ((((((%104 $4) $3)
       $2) $1) $0) $6)) ((((((%104 %214) %215) %216) %217) %218)
       $5)))))))))))))))))`)
  val rexp_nchotomy =
    DT(["DISK_THM"], [],
       `(%74 (\%168. ((%8 ((%76 $0) %90)) ((%8 (%68 (\%181. ((%76 $1) (%91
       $0))))) ((%8 (%219 (\%168. (%219 (\%220. ((%76 $2) ((%92 $1)
       $0))))))) ((%8 (%219 (\%168. (%219 (\%220. ((%76 $2) ((%93 $1)
       $0))))))) (%219 (\%168. ((%76 $1) (%94 $0))))))))))`)
  val rexp_Axiom =
    DT(["DISK_THM"], [],
       `(%95 (\%221. (%97 (\%222. (%223 (\%224. (%223 (\%225. (%226 (\%227.
       (%228 (\%229. ((%17 ((%34 ($0 %90)) $5)) ((%17 (%18 (\%19. ((%34 ($1
       (%91 $0))) ($5 $0))))) ((%17 (%74 (\%85. (%74 (\%86. ((%34 ($2 ((%92
       $1) $0))) (((($5 $1) $0) ($2 $1)) ($2 $0)))))))) ((%17 (%74 (\%85.
       (%74 (\%86. ((%34 ($2 ((%93 $1) $0))) (((($4 $1) $0) ($2 $1)) ($2
       $0)))))))) (%74 (\%75. ((%34 ($1 (%94 $0))) (($2 $0) ($1
       $0)))))))))))))))))))))`)
  val rexp_induction =
    DT(["DISK_THM"], [],
       `(%230 (\%231. ((%6 ((%17 ($0 %90)) ((%17 (%18 (\%181. ($1 (%91
       $0))))) ((%17 (%74 (\%168. (%74 (\%220. ((%6 ((%17 ($2 $1)) ($2
       $0))) ($2 ((%92 $1) $0)))))))) ((%17 (%74 (\%168. (%74 (\%220. ((%6
       ((%17 ($2 $1)) ($2 $0))) ($2 ((%93 $1) $0)))))))) (%74 (\%168. ((%6
       ($1 $0)) ($1 (%94 $0)))))))))) (%74 (\%168. ($1 $0))))))`)
  val starn_ind =
    DT(["DISK_THM"], [],
       `(%232 (\%233. ((%6 ((%17 (%106 (\%137. (($1 $0) %13)))) (%106
       (\%137. (%135 (\%136. ((%6 (%138 (\%115. (%138 (\%112. (%138 (\%116.
       ((%6 ((%17 ((%117 $2) $4)) ((%118 $1) ((%119 $2) $0)))) (($5 $4)
       ((%140 (%16 $3)) (%39 (%40 %41)))))))))))) (($2 $1) (%16 $0)))))))))
       (%106 (\%234. (%135 (\%144. (($2 $1) $0))))))))`)
  val starn_def =
    DT(["DISK_THM"], [],
       `((%17 ((%109 ((%153 %137) %13)) ((%147 %148) %149))) ((%109 ((%153
       %137) (%16 %136))) (%111 (\%112. ((%113 $0) (%114 (\%115. (%114
       (\%116. ((%17 ((%117 $1) %137)) ((%17 ((%117 $0) ((%153 %137) ((%140
       (%16 %136)) (%39 (%40 %41)))))) ((%118 $2) ((%119 $1)
       $0)))))))))))))`)
  val star_rules =
    DT(["DISK_THM"], [],
       `(%106 (\%156. ((%17 ((%155 $0) %148)) ((%17 (%138 (\%112. ((%6
       ((%117 $0) $1)) ((%155 $1) $0))))) (%138 (\%159. (%138 (\%160. ((%6
       ((%17 ((%117 $1) $2)) ((%117 $0) $2))) ((%155 $2) ((%119 $1)
       $0)))))))))))`)
  val star_ind =
    DT(["DISK_THM"], [],
       `(%106 (\%156. (%106 (\%158. ((%6 ((%17 ($0 %148)) ((%17 (%138
       (\%112. ((%6 ((%117 $0) $2)) ($1 $0))))) (%138 (\%159. (%138 (\%160.
       ((%6 ((%17 ((%117 $1) $3)) ((%117 $0) $3))) ($2 ((%119 $1)
       $0)))))))))) (%138 (\%157. ((%6 ((%155 $2) $0)) ($1 $0)))))))))`)
  val star_cases =
    DT(["DISK_THM"], [],
       `(%106 (\%156. (%138 (\%157. ((%24 ((%155 $1) $0)) ((%8 ((%118 $0)
       %148)) ((%8 ((%117 $0) $1)) (%114 (\%159. (%114 (\%160. ((%17 ((%118
       $2) ((%119 $1) $0))) ((%17 ((%117 $1) $3)) ((%117 $0)
       $3))))))))))))))`)
  end
  val _ = DB.bindl "regexp"
  [("symbol_TY_DEF",symbol_TY_DEF,DB.Def),
   ("symbol_repfns",symbol_repfns,DB.Def),
   ("regexp0_def",regexp0_def,DB.Def), ("regexp1_def",regexp1_def,DB.Def),
   ("TS",TS,DB.Def), ("NTS",NTS,DB.Def),
   ("symbol_case_def",symbol_case_def,DB.Def),
   ("symbol_size_def",symbol_size_def,DB.Def),
   ("isTmnlSym_def",isTmnlSym_def,DB.Def),
   ("isNonTmnlSym_def",isNonTmnlSym_def,DB.Def),
   ("tmnlSym_def",tmnlSym_def,DB.Def),
   ("nonTmnlSym_def",nonTmnlSym_def,DB.Def),
   ("nts2str_def",nts2str_def,DB.Def), ("ts2str_def",ts2str_def,DB.Def),
   ("sym2Str_def",sym2Str_def,DB.Def), ("rexp_TY_DEF",rexp_TY_DEF,DB.Def),
   ("rexp_repfns",rexp_repfns,DB.Def), ("regexp2_def",regexp2_def,DB.Def),
   ("regexp3_def",regexp3_def,DB.Def), ("regexp4_def",regexp4_def,DB.Def),
   ("regexp5_def",regexp5_def,DB.Def), ("regexp6_def",regexp6_def,DB.Def),
   ("EmptyLang",EmptyLang,DB.Def), ("Atom",Atom,DB.Def),
   ("Union",Union,DB.Def), ("Conc",Conc,DB.Def), ("Star",Star,DB.Def),
   ("rexp_case_def",rexp_case_def,DB.Def),
   ("rexp_size_def",rexp_size_def,DB.Def), ("conc_def",conc_def,DB.Def),
   ("union_def",union_def,DB.Def),
   ("starn_tupled_primitive_def",starn_tupled_primitive_def,DB.Def),
   ("starn_curried_def",starn_curried_def,DB.Def), ("star",star,DB.Def),
   ("lang_def",lang_def,DB.Def),
   ("datatype_symbol",datatype_symbol,DB.Thm),
   ("symbol_11",symbol_11,DB.Thm),
   ("symbol_distinct",symbol_distinct,DB.Thm),
   ("symbol_case_cong",symbol_case_cong,DB.Thm),
   ("symbol_nchotomy",symbol_nchotomy,DB.Thm),
   ("symbol_Axiom",symbol_Axiom,DB.Thm),
   ("symbol_induction",symbol_induction,DB.Thm),
   ("isTmnlSymML",isTmnlSymML,DB.Thm),
   ("isNonTmnlSymML",isNonTmnlSymML,DB.Thm), ("sym_r1a",sym_r1a,DB.Thm),
   ("sym_r1b",sym_r1b,DB.Thm), ("sym_r2",sym_r2,DB.Thm),
   ("sym_r3",sym_r3,DB.Thm), ("sym_r3b",sym_r3b,DB.Thm),
   ("sym_r4",sym_r4,DB.Thm), ("sym_r4b",sym_r4b,DB.Thm),
   ("sym_r5",sym_r5,DB.Thm), ("sym_r6",sym_r6,DB.Thm),
   ("sym_r7",sym_r7,DB.Thm), ("sym_r7b",sym_r7b,DB.Thm),
   ("rightnt",rightnt,DB.Thm), ("datatype_rexp",datatype_rexp,DB.Thm),
   ("rexp_11",rexp_11,DB.Thm), ("rexp_distinct",rexp_distinct,DB.Thm),
   ("rexp_case_cong",rexp_case_cong,DB.Thm),
   ("rexp_nchotomy",rexp_nchotomy,DB.Thm),
   ("rexp_Axiom",rexp_Axiom,DB.Thm),
   ("rexp_induction",rexp_induction,DB.Thm),
   ("starn_ind",starn_ind,DB.Thm), ("starn_def",starn_def,DB.Thm),
   ("star_rules",star_rules,DB.Thm), ("star_ind",star_ind,DB.Thm),
   ("star_cases",star_cases,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("listLemmasTheory.listLemmas_grammars",
                          listLemmasTheory.listLemmas_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "symbol"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_symbol")
        {Name = "dest_symbol", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_symbol")
        {Name = "mk_symbol", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp0")
        {Name = "regexp0", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp1")
        {Name = "regexp1", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TS")
        {Name = "TS", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NTS")
        {Name = "NTS", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "symbol_case")
        {Name = "symbol_case", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "symbol_size")
        {Name = "symbol_size", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isTmnlSym")
        {Name = "isTmnlSym", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isNonTmnlSym")
        {Name = "isNonTmnlSym", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tmnlSym")
        {Name = "tmnlSym", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nonTmnlSym")
        {Name = "nonTmnlSym", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nts2str")
        {Name = "nts2str", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ts2str")
        {Name = "ts2str", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sym2Str")
        {Name = "sym2Str", Thy = "regexp"}
  val _ = update_grms temp_add_type "rexp"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_rexp")
        {Name = "dest_rexp", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_rexp")
        {Name = "mk_rexp", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp2")
        {Name = "regexp2", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp3")
        {Name = "regexp3", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp4")
        {Name = "regexp4", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp5")
        {Name = "regexp5", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "regexp6")
        {Name = "regexp6", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "EmptyLang")
        {Name = "EmptyLang", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Atom")
        {Name = "Atom", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Union")
        {Name = "Union", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Conc")
        {Name = "Conc", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Star")
        {Name = "Star", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rexp_case")
        {Name = "rexp_case", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rexp_size")
        {Name = "rexp_size", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "conc")
        {Name = "conc", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "union")
        {Name = "union", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "starn_tupled")
        {Name = "starn_tupled", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "starn")
        {Name = "starn", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "star")
        {Name = "star", Thy = "regexp"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lang")
        {Name = "lang", Thy = "regexp"}
  val regexp_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG symbol_Axiom,
           case_def=symbol_case_def,
           case_cong=symbol_case_cong,
           induction=ORIG symbol_induction,
           nchotomy=symbol_nchotomy,
           size=SOME(Parse.Term`(regexp$symbol_size) :(regexp$symbol) -> (num$num)`,
                     ORIG symbol_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME symbol_11,
           distinct=SOME symbol_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];
  
  
  val _ = computeLib.add_funs [isTmnlSym_def];  
  
  val _ = computeLib.add_funs [isNonTmnlSym_def];  
  
  val _ = computeLib.add_funs [tmnlSym_def];  
  
  val _ = computeLib.add_funs [nonTmnlSym_def];  
  
  val _ = computeLib.add_funs [nts2str_def];  
  
  val _ = computeLib.add_funs [ts2str_def];  
  
  val _ = computeLib.add_funs [sym2Str_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG rexp_Axiom,
           case_def=rexp_case_def,
           case_cong=rexp_case_cong,
           induction=ORIG rexp_induction,
           nchotomy=rexp_nchotomy,
           size=SOME(Parse.Term`(regexp$rexp_size) :(regexp$rexp) -> (num$num)`,
                     ORIG rexp_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME rexp_11,
           distinct=SOME rexp_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];
  
  
  val _ = computeLib.add_funs [conc_def];  
  
  val _ = computeLib.add_funs [union_def];  
  
  val _ = computeLib.add_funs [starn_def,
                               (Conv.CONV_RULE TotalDefn.SUC_TO_NUMERAL_DEFN_CONV starn_def)];
  
  
  val _ = computeLib.add_funs [lang_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
