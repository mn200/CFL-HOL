structure grammarDefTheory :> grammarDefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading grammarDefTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open regexpTheory setLemmasTheory
  in end;
  val _ = Theory.link_parents
          ("grammarDef",
          Arbnum.fromString "1203551063",
          Arbnum.fromString "68399")
          [("setLemmas",
           Arbnum.fromString "1203551050",
           Arbnum.fromString "695895"),
           ("regexp",
           Arbnum.fromString "1203551024",
           Arbnum.fromString "43783")];
  val _ = Theory.incorporate_types "grammarDef"
       [("grammar",0), ("rule",0)];
  val _ = Theory.incorporate_consts "grammarDef"
     [("lderives",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list" [T"symbol" "regexp" []] --> bool))))),
      ("llanguage",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
      ("lhsWithNullSfx",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]] -->
          T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
      ("is_null",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
      ("getRules",
       ((T"string" "string" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list" [T"rule" "grammarDef" []])))),
      ("derivesNull",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("rule",
       ((T"string" "string" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          T"rule" "grammarDef" [])))),
      ("allSyms",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("derives",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list" [T"symbol" "regexp" []] --> bool))))),
      ("lhsWithLastSym",
       ((T"symbol" "regexp" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list" [T"symbol" "regexp" []])))),
      ("grammar_size",((T"grammar" "grammarDef" [] --> T"num" "num" []))),
      ("rule_case",
       (((T"string" "string" [] -->
          (T"list" "list" [T"symbol" "regexp" []] --> alpha)) -->
         (T"rule" "grammarDef" [] --> alpha)))),
      ("nonTerminalsML",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("sforms",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
      ("nullableList_tupled_aux",
       (((T"prod" "pair"
           [T"grammar" "grammarDef" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]] -->
          (T"prod" "pair"
            [T"grammar" "grammarDef" [],
             T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
         (T"prod" "pair"
           [T"grammar" "grammarDef" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]] --> bool)))),
      ("rlanguage",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
      ("grammarDef1",
       ((T"list" "list" [T"rule" "grammarDef" []] -->
         (T"string" "string" [] --> T"grammar" "grammarDef" [])))),
      ("grammarDef0",
       ((T"string" "string" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          T"rule" "grammarDef" [])))),
      ("nullable",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
      ("numNonTmnls",
       ((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" []))),
      ("dest_grammar",
       ((T"grammar" "grammarDef" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"rule" "grammarDef" []],
             T"string" "string" []]]))),
      ("sfxNotNull",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list"
           [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
          --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
      ("numTmnls",
       ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" []))),
      ("rule_terminals",
       ((T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))),
      ("ruleRhs",
       ((T"rule" "grammarDef" [] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("lhsWithLastSym_tupled",
       ((T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"symbol" "regexp" []]))),
      ("nonTerminals",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("rules",
       ((T"grammar" "grammarDef" [] -->
         T"list" "list" [T"rule" "grammarDef" []]))),
      ("ruleLhs",((T"rule" "grammarDef" [] --> T"string" "string" []))),
      ("sfxNotNull_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
      ("lhsWithNullSfx_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [T"string" "string" [],
               T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
      ("nr_defn_tupled_aux",
       (((T"prod" "pair"
           [T"grammar" "grammarDef" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]] -->
          (T"prod" "pair"
            [T"grammar" "grammarDef" [],
             T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
         (T"prod" "pair"
           [T"grammar" "grammarDef" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]] --> bool)))),
      ("rulesWithSymInRhs_tupled",
       ((T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         -->
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]))),
      ("rule_size",((T"rule" "grammarDef" [] --> T"num" "num" []))),
      ("nullableList_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool))),
      ("getRhs",
       ((T"string" "string" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
      ("dest_rule",
       ((T"rule" "grammarDef" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]))),
      ("rhsWithSym_tupled",
       ((T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
      ("nr",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list" [T"symbol" "regexp" []] --> bool))))),
      ("language",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
      ("terminals",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("getRules_tupled",
       ((T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"rule" "grammarDef" []]))),
      ("grammar_case",
       (((T"list" "list" [T"rule" "grammarDef" []] -->
          (T"string" "string" [] --> alpha)) -->
         (T"grammar" "grammarDef" [] --> alpha)))),
      ("startSym",
       ((T"grammar" "grammarDef" [] --> T"string" "string" []))),
      ("is_word",((T"list" "list" [T"symbol" "regexp" []] --> bool))),
      ("rulesWithSymInRhs",
       ((T"symbol" "regexp" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]])))),
      ("allSymsML",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("mk_rule",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]] -->
         T"rule" "grammarDef" []))),
      ("getRhs_tupled",
       ((T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
      ("rderives",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list" [T"symbol" "regexp" []] --> bool))))),
      ("gaw",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("nullableML",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list" [T"symbol" "regexp" []] --> bool))))),
      ("mk_grammar",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"rule" "grammarDef" []],
             T"string" "string" []]] --> T"grammar" "grammarDef" []))),
      ("G",
       ((T"list" "list" [T"rule" "grammarDef" []] -->
         (T"string" "string" [] --> T"grammar" "grammarDef" [])))),
      ("rule_nonterminals",
       ((T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))),
      ("terminalsML",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("nr_defn_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool))),
      ("rhsWithSym",
       ((T"symbol" "regexp" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"rule" "grammarDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]]) --> bool) --> bool)),
   V"rep"
    ((T"rule" "grammarDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"list" "list" [T"symbol" "regexp" []]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> bool) -->
      ((T"rule" "grammarDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
        --> bool) --> bool) --> bool)),
   V"'rule'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
      --> bool)), C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> bool) --> bool)),
   C"?" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"a0" (T"string" "string" []),
   C"?" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"a1" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
      -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]])))),
   C"0" "num" (T"num" "num" []),
   C"," "pair"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]))),
   V"n" (T"num" "num" []),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   V"a" (T"rule" "grammarDef" []),
   C"=" "min"
    ((T"rule" "grammarDef" [] --> (T"rule" "grammarDef" [] --> bool))),
   C"mk_rule" "grammarDef"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
      --> T"rule" "grammarDef" [])),
   C"dest_rule" "grammarDef"
    ((T"rule" "grammarDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"list" "list" [T"symbol" "regexp" []]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"rule" "grammarDef" [])) -->
      ((T"string" "string" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"rule" "grammarDef" [])) --> bool))),
   C"grammarDef0" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   C"!" "bool"
    ((((T"string" "string" [] -->
        (T"list" "list" [T"symbol" "regexp" []] --> alpha)) --> bool) -->
      bool)),
   V"f"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> alpha))),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] --> alpha)) -->
      (T"rule" "grammarDef" [] --> alpha))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"rule_size" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"string_size" "string" ((T"string" "string" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"symbol" "regexp" [] --> T"num" "num" []) -->
      (T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" []))),
   C"symbol_size" "regexp" ((T"symbol" "regexp" [] --> T"num" "num" [])),
   C"?" "bool"
    ((((T"grammar" "grammarDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"rule" "grammarDef" []],
            T"string" "string" []]]) --> bool) --> bool)),
   V"rep"
    ((T"grammar" "grammarDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []],
          T"string" "string" []]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []],
           T"string" "string" []]] --> bool) -->
      ((T"grammar" "grammarDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"rule" "grammarDef" []],
            T"string" "string" []]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []],
         T"string" "string" []]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"rule" "grammarDef" []],
            T"string" "string" []]] --> bool) --> bool) --> bool)),
   V"'grammar'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]]
      --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []],
           T"string" "string" []]] --> bool) --> bool)),
   C"?" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] --> bool) --> bool)),
   V"a0" (T"list" "list" [T"rule" "grammarDef" []]),
   V"a1" (T"string" "string" []),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]]
      -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []],
           T"string" "string" []]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"list" "list" [T"rule" "grammarDef" []],
             T"string" "string" []]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"list" "list" [T"rule" "grammarDef" []],
            T"string" "string" []]])))),
   C"," "pair"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] -->
       T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []],
         T"string" "string" []]))),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []],
         T"string" "string" []]]),
   C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"a" (T"grammar" "grammarDef" []),
   C"=" "min"
    ((T"grammar" "grammarDef" [] -->
      (T"grammar" "grammarDef" [] --> bool))),
   C"mk_grammar" "grammarDef"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]]
      --> T"grammar" "grammarDef" [])),
   C"dest_grammar" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []],
          T"string" "string" []]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []],
         T"string" "string" []]]),
   C"=" "min"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"string" "string" [] --> T"grammar" "grammarDef" [])) -->
      ((T"list" "list" [T"rule" "grammarDef" []] -->
        (T"string" "string" [] --> T"grammar" "grammarDef" [])) -->
       bool))),
   C"grammarDef1" "grammarDef"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] --> T"grammar" "grammarDef" []))),
   C"G" "grammarDef"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] --> T"grammar" "grammarDef" []))),
   C"!" "bool"
    ((((T"list" "list" [T"rule" "grammarDef" []] -->
        (T"string" "string" [] --> alpha)) --> bool) --> bool)),
   V"f"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] --> alpha))),
   C"!" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] --> bool) --> bool)),
   C"grammar_case" "grammarDef"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"string" "string" [] --> alpha)) -->
      (T"grammar" "grammarDef" [] --> alpha))),
   C"grammar_size" "grammarDef"
    ((T"grammar" "grammarDef" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"rule" "grammarDef" [] --> T"num" "num" []) -->
      (T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" []))),
   V"l" (T"string" "string" []),
   V"r" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"ruleRhs" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"=" "min"
    ((T"string" "string" [] --> (T"string" "string" [] --> bool))),
   C"ruleLhs" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"string" "string" [])),
   C"=" "min"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"rule" "grammarDef" []]) -->
      ((T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"rule" "grammarDef" []]) --> bool))),
   C"getRules_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"rule" "grammarDef" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"rule" "grammarDef" []]) -->
        (T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"rule" "grammarDef" []])) -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"rule" "grammarDef" []])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        -->
        (T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) --> bool)),
   V"rs" (T"list" "list" [T"rule" "grammarDef" []]),
   V"sym" (T"string" "string" []), C"~" "bool" ((bool --> bool)),
   C"," "pair"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"string" "string" [],
         T"list" "list" [T"rule" "grammarDef" []]]))),
   C"CONS" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   V"getRules_tupled"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"rule" "grammarDef" []])),
   V"a"
    (T"prod" "pair"
      [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]),
   C"pair_case" "pair"
    (((T"string" "string" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"rule" "grammarDef" []])) -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"rule" "grammarDef" []]))),
   V"v1" (T"list" "list" [T"rule" "grammarDef" []]),
   C"list_case" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   C"I" "combin"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"NIL" "list" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v2" (T"rule" "grammarDef" []),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"rule" "grammarDef" []])) -->
      (T"rule" "grammarDef" [] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   V"x" (T"string" "string" []),
   V"x1" (T"list" "list" [T"rule" "grammarDef" []]),
   C"=" "min"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"getRules" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
      ((T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
       bool))),
   C"rhsWithSym_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
        (T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        -->
        (T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      -->
      (T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) --> bool)),
   V"rst" (T"list" "list" [T"rule" "grammarDef" []]),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"sym" (T"symbol" "regexp" []),
   C"MEM" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"symbol" "regexp" [],
         T"list" "list" [T"rule" "grammarDef" []]]))),
   V"rhsWithSym_tupled"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   V"a"
    (T"prod" "pair"
      [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]),
   C"pair_case" "pair"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"list_case" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   C"I" "combin"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   C"NIL" "list" (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"rule" "grammarDef" [] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
       (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   C"CONS" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   V"x" (T"symbol" "regexp" []),
   C"=" "min"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   C"rhsWithSym" "grammarDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]])
      -->
      ((T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        -->
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]]) --> bool))),
   C"rulesWithSymInRhs_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      -->
      T"list" "list"
       [T"prod" "pair"
         [T"string" "string" [],
          T"list" "list" [T"symbol" "regexp" []]]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         -->
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]) -->
        (T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         -->
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]])) -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        -->
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]])))),
   V"rulesWithSymInRhs_tupled"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      -->
      T"list" "list"
       [T"prod" "pair"
         [T"string" "string" [],
          T"list" "list" [T"symbol" "regexp" []]]])),
   C"pair_case" "pair"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]])) -->
      (T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [],
           T"list" "list" [T"symbol" "regexp" []]]]))),
   C"list_case" "list"
    ((T"list" "list"
       [T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
      -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]])))),
   C"I" "combin"
    ((T"list" "list"
       [T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
      -->
      T"list" "list"
       [T"prod" "pair"
         [T"string" "string" [],
          T"list" "list" [T"symbol" "regexp" []]]])),
   C"NIL" "list"
    (T"list" "list"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]])) -->
      (T"rule" "grammarDef" [] -->
       T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [],
           T"list" "list" [T"symbol" "regexp" []]]]))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
        -->
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]])))),
   C"CONS" "list"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]] -->
      (T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       -->
       T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [],
           T"list" "list" [T"symbol" "regexp" []]]]))),
   C"breakAtElem" "listLemmas"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"=" "min"
    ((T"list" "list"
       [T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
      -->
      (T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> bool))),
   C"rulesWithSymInRhs" "grammarDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [],
           T"list" "list" [T"symbol" "regexp" []]]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"symbol" "regexp" []]) -->
      ((T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"symbol" "regexp" []]) --> bool))),
   C"lhsWithLastSym_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"symbol" "regexp" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"symbol" "regexp" []]) -->
        (T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"symbol" "regexp" []])) -->
       (T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"symbol" "regexp" []])))),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   V"v7" (T"list" "list" [T"symbol" "regexp" []]),
   V"v6" (T"symbol" "regexp" []),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"LAST" "list"
    ((T"list" "list" [T"symbol" "regexp" []] --> T"symbol" "regexp" [])),
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"lhsWithLastSym_tupled"
    ((T"prod" "pair"
       [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"symbol" "regexp" []])),
   C"pair_case" "pair"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"symbol" "regexp" []]))),
   C"list_case" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"I" "combin"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"rule" "grammarDef" [] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"v5" (T"list" "list" [T"symbol" "regexp" []]),
   C"list_case" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"rmDupes" "listLemmas"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   V"v8" (T"symbol" "regexp" []),
   V"v9" (T"list" "list" [T"symbol" "regexp" []]),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"lhsWithLastSym" "grammarDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"=" "min"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   C"rule_terminals" "grammarDef"
    ((T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"GSPEC" "pred_set"
    (((T"symbol" "regexp" [] -->
       T"prod" "pair" [T"symbol" "regexp" [], bool]) -->
      (T"symbol" "regexp" [] --> bool))), V"tmnl" (T"symbol" "regexp" []),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (bool --> T"prod" "pair" [T"symbol" "regexp" [], bool]))),
   C"isTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   C"rule_nonterminals" "grammarDef"
    ((T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"INSERT" "pred_set"
    ((T"symbol" "regexp" [] -->
      ((T"symbol" "regexp" [] --> bool) -->
       (T"symbol" "regexp" [] --> bool)))), V"nt" (T"symbol" "regexp" []),
   C"isNonTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   V"w" (T"list" "list" [T"symbol" "regexp" []]),
   C"is_word" "grammarDef"
    ((T"list" "list" [T"symbol" "regexp" []] --> bool)),
   C"EVERY" "list"
    (((T"symbol" "regexp" [] --> bool) -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   V"p" (T"list" "list" [T"rule" "grammarDef" []]),
   V"s" (T"string" "string" []),
   C"rules" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"startSym" "grammarDef"
    ((T"grammar" "grammarDef" [] --> T"string" "string" [])),
   C"terminals" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"BIGUNION" "pred_set"
    ((((T"symbol" "regexp" [] --> bool) --> bool) -->
      (T"symbol" "regexp" [] --> bool))),
   C"IMAGE" "pred_set"
    (((T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)) -->
      ((T"rule" "grammarDef" [] --> bool) -->
       ((T"symbol" "regexp" [] --> bool) --> bool)))),
   C"LIST_TO_SET" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"rule" "grammarDef" [] --> bool))),
   C"nonTerminals" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"=" "min"
    (((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)) -->
      ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))
       --> bool))),
   C"nonTerminalsML" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"WFREC" "relation"
    (((T"grammar" "grammarDef" [] -->
       (T"grammar" "grammarDef" [] --> bool)) -->
      (((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))
        -->
        (T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))
       -->
       (T"grammar" "grammarDef" [] -->
        (T"symbol" "regexp" [] --> bool))))),
   C"@" "min"
    ((((T"grammar" "grammarDef" [] -->
        (T"grammar" "grammarDef" [] --> bool)) --> bool) -->
      (T"grammar" "grammarDef" [] -->
       (T"grammar" "grammarDef" [] --> bool)))),
   V"R"
    ((T"grammar" "grammarDef" [] -->
      (T"grammar" "grammarDef" [] --> bool))),
   C"WF" "relation"
    (((T"grammar" "grammarDef" [] -->
       (T"grammar" "grammarDef" [] --> bool)) --> bool)),
   V"nonTerminalsML"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"grammar_case" "grammarDef"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"string" "string" [] --> (T"symbol" "regexp" [] --> bool))) -->
      (T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))),
   V"v" (T"list" "list" [T"rule" "grammarDef" []]),
   C"list_case" "list"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         (T"symbol" "regexp" [] --> bool))) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        (T"symbol" "regexp" [] --> bool))))),
   C"I" "combin"
    (((T"symbol" "regexp" [] --> bool) -->
      (T"symbol" "regexp" [] --> bool))),
   C"LIST_TO_SET" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"symbol" "regexp" [] --> bool))),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        (T"symbol" "regexp" [] --> bool))) -->
      (T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))),
   C"UNION" "pred_set"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] --> bool) -->
       (T"symbol" "regexp" [] --> bool)))),
   C"FILTER" "list"
    (((T"symbol" "regexp" [] --> bool) -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"APPEND" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"terminalsML" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   V"terminalsML"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   V"g" (T"grammar" "grammarDef" []),
   C"allSyms" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"allSymsML" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   V"lsl" (T"list" "list" [T"symbol" "regexp" []]),
   V"rsl" (T"list" "list" [T"symbol" "regexp" []]),
   C"derives" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   V"s1" (T"list" "list" [T"symbol" "regexp" []]),
   V"s2" (T"list" "list" [T"symbol" "regexp" []]),
   V"rhs" (T"list" "list" [T"symbol" "regexp" []]),
   V"lhs" (T"string" "string" []),
   C"MEM" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"lderives" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"rderives" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"gaw" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"RTC" "relation"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"=" "min"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) -->
      ((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool))),
   C"sforms" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"GSPEC" "pred_set"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       T"prod" "pair" [T"list" "list" [T"symbol" "regexp" []], bool]) -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   V"tsl" (T"list" "list" [T"symbol" "regexp" []]),
   C"," "pair"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (bool -->
       T"prod" "pair" [T"list" "list" [T"symbol" "regexp" []], bool]))),
   C"language" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"llanguage" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"rlanguage" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"is_null" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"numTmnls" "grammarDef"
    ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" [])),
   V"r" (T"symbol" "regexp" []),
   V"rs" (T"list" "list" [T"symbol" "regexp" []]),
   C"COND" "bool"
    ((bool -->
      (T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" [])))),
   V"sl" (T"list" "list" [T"symbol" "regexp" []]),
   C"nullable" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"!" "bool"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool)) --> bool)
      --> bool)),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] --> bool))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] --> bool) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool) --> bool))),
   C"nr_defn_tupled_aux" "grammarDef"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] --> bool))),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool)))),
   V"nr_defn_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] --> bool)),
   V"a"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] --> bool)) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] --> bool))),
   V"v2"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   V"v0" (T"list" "list" [T"symbol" "regexp" []]),
   V"v4" (T"list" "list" [T"symbol" "regexp" []]),
   C"list_case" "list"
    ((bool -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"I" "combin" ((bool --> bool)), C"T" "bool" (bool),
   V"v5" (T"symbol" "regexp" []),
   V"v6" (T"list" "list" [T"symbol" "regexp" []]),
   C"symbol_case" "regexp"
    (((T"string" "string" [] --> bool) -->
      ((T"string" "string" [] --> bool) -->
       (T"symbol" "regexp" [] --> bool)))), V"ts" (T"string" "string" []),
   C"F" "bool" (bool), V"v13" (T"symbol" "regexp" []),
   V"v14" (T"list" "list" [T"symbol" "regexp" []]),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]]))),
   C"," "pair"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]]))),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   V"nt" (T"string" "string" []),
   C"COND" "bool" ((bool --> (bool --> (bool --> bool)))),
   C"INTER" "pred_set"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] --> bool) -->
       (T"symbol" "regexp" [] --> bool)))),
   C"EMPTY" "pred_set" ((T"symbol" "regexp" [] --> bool)),
   V"v17" (T"symbol" "regexp" []),
   V"v18" (T"list" "list" [T"symbol" "regexp" []]),
   C"nr_defn_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] --> bool)),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool)))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool)) --> bool)),
   V"sn" (T"list" "list" [T"symbol" "regexp" []]),
   V"v16" (T"list" "list" [T"symbol" "regexp" []]),
   V"v15" (T"symbol" "regexp" []), V"v8" (T"string" "string" []),
   C"RESTRICT" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] --> bool) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool))))),
   V"v12" (T"list" "list" [T"symbol" "regexp" []]),
   V"v11" (T"symbol" "regexp" []), V"v7" (T"string" "string" []),
   V"x" (T"grammar" "grammarDef" []),
   V"x1" (T"list" "list" [T"symbol" "regexp" []]),
   V"x2" (T"list" "list" [T"symbol" "regexp" []]),
   C"nr" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"=" "min"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
      ((T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
       bool))),
   C"getRhs_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
        (T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   V"l'" (T"string" "string" []),
   V"getRhs_tupled"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   C"pair_case" "pair"
    (((T"string" "string" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"APPEND" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"getRhs" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"derivesNull" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"=" "min"
    (((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" []) -->
      ((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" []) -->
       bool))),
   C"numNonTmnls" "grammarDef"
    ((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])),
   C"WFREC" "relation"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)) -->
      (((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" []) -->
        (T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])) -->
       (T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])))),
   C"@" "min"
    ((((T"list" "list" [T"rule" "grammarDef" []] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> bool)) --> bool) -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)))),
   V"R"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"WF" "relation"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)) --> bool)),
   V"numNonTmnls"
    ((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])),
   V"a" (T"list" "list" [T"rule" "grammarDef" []]),
   C"list_case" "list"
    ((T"num" "num" [] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])) -->
       (T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])))),
   C"I" "combin" ((T"num" "num" [] --> T"num" "num" [])),
   V"v" (T"rule" "grammarDef" []),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" [])) -->
      (T"rule" "grammarDef" [] --> T"num" "num" []))),
   C"LENGTH" "list"
    ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" [])),
   C"nullableList_tupled_aux" "grammarDef"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] --> bool)) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] --> bool))),
   V"nullableList_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] --> bool)),
   V"a'"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]]]),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   V"v3" (T"list" "list" [T"symbol" "regexp" []]),
   V"v4" (T"symbol" "regexp" []), V"v12" (T"symbol" "regexp" []),
   V"v13" (T"list" "list" [T"symbol" "regexp" []]),
   V"A" (T"string" "string" []),
   C"EXISTS" "list"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   V"a" (T"list" "list" [T"symbol" "regexp" []]),
   V"v16" (T"symbol" "regexp" []),
   V"v17" (T"list" "list" [T"symbol" "regexp" []]),
   C"nullableList_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] --> bool)),
   C"MEM" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   V"v15" (T"list" "list" [T"symbol" "regexp" []]),
   V"v14" (T"symbol" "regexp" []),
   V"v11" (T"list" "list" [T"symbol" "regexp" []]),
   V"v10" (T"symbol" "regexp" []), V"v6" (T"string" "string" []),
   C"nullableML" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]]] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
       bool))),
   C"lhsWithNullSfx_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]]] -->
      T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [T"string" "string" [],
               T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [T"string" "string" [],
               T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]]] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [T"string" "string" [],
               T"list" "list" [T"symbol" "regexp" []]]]] --> bool)) -->
       bool) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]]] -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [T"string" "string" [],
              T"list" "list" [T"symbol" "regexp" []]]]] --> bool)) -->
      bool)),
   C"!" "bool"
    (((T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> bool) --> bool)),
   V"rst"
    (T"list" "list"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   V"sfx" (T"list" "list" [T"symbol" "regexp" []]),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]]))),
   V"lhsWithNullSfx_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [],
            T"list" "list" [T"symbol" "regexp" []]]]] -->
      T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   V"a"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [],
           T"list" "list" [T"symbol" "regexp" []]]]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   V"v1"
    (T"list" "list"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   C"list_case" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      ((T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]
        -->
        (T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"list" "list"
         [T"prod" "pair"
           [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   V"v2"
    (T"prod" "pair"
      [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]),
   C"pair_case" "pair"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   V"x1"
    (T"list" "list"
      [T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]),
   C"lhsWithNullSfx" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
       bool))),
   C"sfxNotNull_tupled" "grammarDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list"
         [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
      --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [alpha, T"list" "list" [T"symbol" "regexp" []]]]] --> bool))
      -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list"
            [T"prod" "pair"
              [alpha, T"list" "list" [T"symbol" "regexp" []]]]] --> bool))
       --> bool) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [alpha, T"list" "list" [T"symbol" "regexp" []]]]] -->
        bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list"
         [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list"
           [T"prod" "pair"
             [alpha, T"list" "list" [T"symbol" "regexp" []]]]] --> bool))
      --> bool)), C"!" "bool" (((alpha --> bool) --> bool)), V"l" (alpha),
   C"!" "bool"
    (((T"list" "list"
        [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
       --> bool) --> bool)),
   V"rst"
    (T"list" "list"
      [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
       -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair"
            [alpha, T"list" "list" [T"symbol" "regexp" []]]]]))),
   C"CONS" "list"
    ((T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]] -->
      (T"list" "list"
        [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
       -->
       T"list" "list"
        [T"prod" "pair"
          [alpha, T"list" "list" [T"symbol" "regexp" []]]]))),
   C"," "pair"
    ((alpha -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]))),
   V"sfxNotNull_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list"
         [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
      --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])),
   V"a"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"list" "list"
        [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"list" "list"
         [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   V"v1"
    (T"list" "list"
      [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]),
   C"list_case" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      ((T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]] -->
        (T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
         --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
       (T"list" "list"
         [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
        --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])))),
   V"v2" (T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]),
   C"pair_case" "pair"
    (((alpha -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"list" "list" [T"symbol" "regexp" []]])) -->
      (T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   V"x1"
    (T"list" "list"
      [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]),
   C"sfxNotNull" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
       --> T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"rule"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"rule" "grammarDef" [])) --> bool)),
   V"a0'" (T"string" "string" []),
   V"a1'" (T"list" "list" [T"symbol" "regexp" []]),
   V"M" (T"rule" "grammarDef" []), V"M'" (T"rule" "grammarDef" []),
   V"f'"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> alpha))),
   V"r" (T"rule" "grammarDef" []),
   V"l" (T"list" "list" [T"symbol" "regexp" []]),
   C"?" "bool" ((((T"rule" "grammarDef" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"rule" "grammarDef" [] --> alpha)),
   C"!" "bool" ((((T"rule" "grammarDef" [] --> bool) --> bool) --> bool)),
   V"P" ((T"rule" "grammarDef" [] --> bool)),
   V"grammar"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"string" "string" [] --> T"grammar" "grammarDef" [])) --> bool)),
   V"a0'" (T"list" "list" [T"rule" "grammarDef" []]),
   V"a1'" (T"string" "string" []), V"M" (T"grammar" "grammarDef" []),
   V"M'" (T"grammar" "grammarDef" []),
   V"f'"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] --> alpha))),
   V"l" (T"list" "list" [T"rule" "grammarDef" []]),
   C"?" "bool"
    ((((T"grammar" "grammarDef" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"grammar" "grammarDef" [] --> alpha)),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] --> bool) --> bool) --> bool)),
   V"P" ((T"grammar" "grammarDef" [] --> bool)),
   C"!" "bool"
    ((((T"string" "string" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> bool)) --> bool) -->
      bool)),
   V"P"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   V"v" (T"string" "string" []),
   C"!" "bool"
    ((((T"symbol" "regexp" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> bool)) --> bool) -->
      bool)),
   V"P"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   V"v" (T"symbol" "regexp" []),
   C"\\/" "bool" ((bool --> (bool --> bool))),
   V"pfx" (T"list" "list" [T"symbol" "regexp" []]),
   V"v" (T"grammar" "grammarDef" []),
   V"u" (T"list" "list" [T"symbol" "regexp" []]),
   V"v" (T"list" "list" [T"symbol" "regexp" []]),
   V"x" (T"list" "list" [T"symbol" "regexp" []]),
   V"rst" (T"list" "list" [T"symbol" "regexp" []]),
   V"fst" (T"symbol" "regexp" []),
   V"M" (T"list" "list" [T"symbol" "regexp" []]),
   V"N" (T"list" "list" [T"symbol" "regexp" []]),
   V"P" (T"list" "list" [T"symbol" "regexp" []]),
   V"Q" (T"list" "list" [T"symbol" "regexp" []]),
   V"b" (T"list" "list" [T"symbol" "regexp" []]),
   V"c" (T"list" "list" [T"symbol" "regexp" []]),
   V"r1" (T"list" "list" [T"symbol" "regexp" []]),
   V"r2" (T"list" "list" [T"symbol" "regexp" []]),
   V"symlist" (T"list" "list" [T"symbol" "regexp" []]),
   V"z" (T"list" "list" [T"symbol" "regexp" []]),
   V"y" (T"list" "list" [T"symbol" "regexp" []]),
   V"x'" (T"list" "list" [T"symbol" "regexp" []]),
   V"y'" (T"list" "list" [T"symbol" "regexp" []]),
   V"rhs" (T"string" "string" []),
   V"lhs'" (T"list" "list" [T"symbol" "regexp" []]),
   V"sf" (T"list" "list" [T"symbol" "regexp" []]),
   V"s" (T"list" "list" [T"symbol" "regexp" []]),
   V"s'" (T"list" "list" [T"symbol" "regexp" []]), V"s1'" (alpha),
   C"!" "bool" (((beta --> bool) --> bool)), V"s2'" (beta),
   V"s1'" (T"list" "list" [T"symbol" "regexp" []]),
   V"s2'" (T"list" "list" [T"symbol" "regexp" []]),
   V"z'" (T"list" "list" [T"symbol" "regexp" []]),
   C"IN" "bool"
    ((T"symbol" "regexp" [] -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   V"p" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min" (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"EMPTY" "pred_set" ((alpha --> bool)),
   C"LIST_TO_SET" "list" ((T"list" "list" [alpha] --> (alpha --> bool))),
   V"l" (T"list" "list" [alpha]),
   C"=" "min"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"NIL" "list" (T"list" "list" [alpha]),
   V"s" ((T"rule" "grammarDef" [] --> bool)),
   C"FINITE" "pred_set" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   C"=" "min"
    (((T"rule" "grammarDef" [] --> bool) -->
      ((T"rule" "grammarDef" [] --> bool) --> bool))),
   C"FINITE" "pred_set" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"e" (T"symbol" "regexp" []),
   C"?" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   C"!" "bool"
    ((((T"list" "list" [T"rule" "grammarDef" []] --> bool) --> bool) -->
      bool)), V"P" ((T"list" "list" [T"rule" "grammarDef" []] --> bool)),
   V"l1" (T"list" "list" [T"rule" "grammarDef" []]),
   V"l2" (T"list" "list" [T"rule" "grammarDef" []]),
   C"APPEND" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   V"e" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool))) --> bool) -->
      bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   V"v1" (T"list" "list" [T"symbol" "regexp" []]),
   V"v2" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list"
          [T"prod" "pair"
            [T"string" "string" [],
             T"list" "list" [T"symbol" "regexp" []]]] --> bool)) --> bool)
      --> bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"symbol" "regexp" []]]]
       --> bool))),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list"
          [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
         --> bool)) --> bool) --> bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]
       --> bool))),
   C"NIL" "list"
    (T"list" "list"
      [T"prod" "pair" [alpha, T"list" "list" [T"symbol" "regexp" []]]]),
   V"tl" (alpha), V"l1" (T"list" "list" [T"symbol" "regexp" []]),
   V"l2" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   C"?" "bool" (((alpha --> bool) --> bool)), V"e" (alpha),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool))),
   V"l" (beta), V"h" (T"symbol" "regexp" []),
   V"tl" (T"list" "list" [T"symbol" "regexp" []]),
   V"l0" (T"list" "list" [T"symbol" "regexp" []]),
   V"l'" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   C"NRC" "arithmetic"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
      (T"num" "num" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        (T"list" "list" [T"symbol" "regexp" []] --> bool))))),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" []))]
  val DT = Thm.disk_thm share_table
  in
  val rule_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 (%8 (\%9. (%10
       (\%11. ((%12 $2) (((\%9. (\%11. (((%13 %14) ((%15 $1) $0)) (\%16.
       %17)))) $1) $0))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val rule_repfns =
    DT(["DISK_THM"], [],
       `((%18 (%19 (\%20. ((%21 (%22 (%23 $0))) $0)))) (%7 (\%24. ((%25
       ((\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 (%8 (\%9. (%10 (\%11. ((%12 $2)
       (((\%9. (\%11. (((%13 %14) ((%15 $1) $0)) (\%16. %17)))) $1)
       $0))))))) ($1 $0))))) ($0 $1))))) $0)) ((%12 (%23 (%22 $0)))
       $0)))))`)
  val grammarDef0_def =
    DT([], [],
       `((%26 %27) (\%9. (\%11. (%22 (((\%9. (\%11. (((%13 %14) ((%15 $1)
       $0)) (\%16. %17)))) $1) $0)))))`)
  val rule = DT([], [], `((%26 %28) %27)`)
  val rule_case_def =
    DT(["DISK_THM"], [],
       `(%29 (\%30. (%31 (\%9. (%32 (\%11. ((%33 ((%34 $2) ((%28 $1) $0)))
       (($2 $1) $0))))))))`)
  val rule_size_def =
    DT(["DISK_THM"], [],
       `(%31 (\%9. (%32 (\%11. ((%35 (%36 ((%28 $1) $0))) ((%37 (%38 (%39
       %40))) ((%37 (%41 $1)) ((%42 %43) $0))))))))`)
  val grammar_TY_DEF =
    DT(["DISK_THM"], [],
       `(%44 (\%45. ((%46 (\%47. (%48 (\%49. ((%6 (%50 (\%47. ((%6 (%51
       (\%52. (%8 (\%53. ((%54 $2) (((\%52. (\%53. (((%55 %14) ((%56 $1)
       $0)) (\%16. %57)))) $1) $0))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val grammar_repfns =
    DT(["DISK_THM"], [],
       `((%18 (%58 (\%59. ((%60 (%61 (%62 $0))) $0)))) (%50 (\%63. ((%25
       ((\%47. (%48 (\%49. ((%6 (%50 (\%47. ((%6 (%51 (\%52. (%8 (\%53.
       ((%54 $2) (((\%52. (\%53. (((%55 %14) ((%56 $1) $0)) (\%16. %57))))
       $1) $0))))))) ($1 $0))))) ($0 $1))))) $0)) ((%54 (%62 (%61 $0)))
       $0)))))`)
  val grammarDef1_def =
    DT([], [],
       `((%64 %65) (\%52. (\%53. (%61 (((\%52. (\%53. (((%55 %14) ((%56 $1)
       $0)) (\%16. %57)))) $1) $0)))))`)
  val G = DT([], [], `((%64 %66) %65)`)
  val grammar_case_def =
    DT(["DISK_THM"], [],
       `(%67 (\%68. (%69 (\%52. (%31 (\%53. ((%33 ((%70 $2) ((%66 $1) $0)))
       (($2 $1) $0))))))))`)
  val grammar_size_def =
    DT(["DISK_THM"], [],
       `(%69 (\%52. (%31 (\%53. ((%35 (%71 ((%66 $1) $0))) ((%37 (%38 (%39
       %40))) ((%37 ((%72 %36) $1)) (%41 $0))))))))`)
  val ruleRhs_def =
    DT(["DISK_THM"], [],
       `(%31 (\%73. (%32 (\%74. ((%75 (%76 ((%28 $1) $0))) $0)))))`)
  val ruleLhs_def =
    DT(["DISK_THM"], [],
       `(%31 (\%73. (%32 (\%74. ((%77 (%78 ((%28 $1) $0))) $1)))))`)
  val getRules_tupled_primitive_def =
    DT([], [],
       `((%79 %80) ((%81 (%82 (\%83. ((%18 (%84 $0)) ((%18 (%32 (\%74. (%69
       (\%85. (%31 (\%73. (%31 (\%86. ((%6 (%87 ((%77 $0) $1))) (($4 ((%88
       $0) $2)) ((%88 $0) ((%89 ((%28 $1) $3)) $2))))))))))))) (%32 (\%74.
       (%69 (\%85. (%31 (\%73. (%31 (\%86. ((%6 ((%77 $0) $1)) (($4 ((%88
       $0) $2)) ((%88 $0) ((%89 ((%28 $1) $3)) $2))))))))))))))))) (\%90.
       (\%91. ((%92 (\%86. (\%93. (((%94 (%95 %96)) (\%97. (\%85. ((%98
       (\%73. (\%74. (%95 (((%99 ((%77 $5) $1)) ((%89 ((%28 $1) $0)) ($7
       ((%88 $5) $2)))) ($7 ((%88 $5) $2))))))) $1)))) $0)))) $0)))))`)
  val getRules_curried_def =
    DT([], [],
       `(%31 (\%100. (%69 (\%101. ((%102 ((%103 $1) $0)) (%80 ((%88 $1)
       $0)))))))`)
  val rhsWithSym_tupled_primitive_def =
    DT([], [],
       `((%104 %105) ((%106 (%107 (\%108. ((%18 (%109 $0)) ((%18 (%31
       (\%73. (%69 (\%110. (%32 (\%74. (%111 (\%112. ((%6 (%87 ((%113 $0)
       $1))) (($4 ((%114 $0) $2)) ((%114 $0) ((%89 ((%28 $3) $1))
       $2))))))))))))) (%31 (\%73. (%69 (\%110. (%32 (\%74. (%111 (\%112.
       ((%6 ((%113 $0) $1)) (($4 ((%114 $0) $2)) ((%114 $0) ((%89 ((%28 $3)
       $1)) $2))))))))))))))))) (\%115. (\%116. ((%117 (\%112. (\%93.
       (((%118 (%119 %120)) (\%97. (\%110. ((%121 (\%73. (\%74. (%119
       (((%122 ((%113 $5) $0)) ((%123 $0) ($7 ((%114 $5) $2)))) ($7 ((%114
       $5) $2))))))) $1)))) $0)))) $0)))))`)
  val rhsWithSym_curried_def =
    DT([], [],
       `(%111 (\%124. (%69 (\%101. ((%125 ((%126 $1) $0)) (%105 ((%114 $1)
       $0)))))))`)
  val rulesWithSymInRhs_tupled_primitive_def =
    DT([], [],
       `((%127 %128) ((%129 (%107 (\%108. ((%18 (%109 $0)) ((%18 (%31
       (\%73. (%69 (\%110. (%32 (\%74. (%111 (\%112. ((%6 (%87 ((%113 $0)
       $1))) (($4 ((%114 $0) $2)) ((%114 $0) ((%89 ((%28 $3) $1))
       $2))))))))))))) (%31 (\%73. (%69 (\%110. (%32 (\%74. (%111 (\%112.
       ((%6 ((%113 $0) $1)) (($4 ((%114 $0) $2)) ((%114 $0) ((%89 ((%28 $3)
       $1)) $2))))))))))))))))) (\%130. (\%116. ((%131 (\%112. (\%93.
       (((%132 (%133 %134)) (\%97. (\%110. ((%135 (\%73. (\%74. (%133
       (((%136 ((%113 $5) $0)) ((%137 ((%15 $1) ((%138 $5) $0))) ($7 ((%114
       $5) $2)))) ($7 ((%114 $5) $2))))))) $1)))) $0)))) $0)))))`)
  val rulesWithSymInRhs_curried_def =
    DT([], [],
       `(%111 (\%124. (%69 (\%101. ((%139 ((%140 $1) $0)) (%128 ((%114 $1)
       $0)))))))`)
  val lhsWithLastSym_tupled_primitive_def =
    DT([], [],
       `((%141 %142) ((%143 (%107 (\%108. ((%18 (%109 $0)) ((%18 (%31
       (\%73. (%69 (\%85. (%111 (\%112. (($3 ((%114 $0) $1)) ((%114 $0)
       ((%89 ((%28 $2) %144)) $1)))))))))) ((%18 (%31 (\%73. (%69 (\%85.
       (%111 (\%112. (%32 (\%145. (%111 (\%146. ((%6 (%87 ((%147 (%148
       ((%149 $0) $1))) $2))) (($5 ((%114 $2) $3)) ((%114 $2) ((%89 ((%28
       $4) ((%149 $0) $1))) $3))))))))))))))) (%31 (\%73. (%69 (\%85. (%111
       (\%112. (%32 (\%145. (%111 (\%146. ((%6 ((%147 (%148 ((%149 $0)
       $1))) $2)) (($5 ((%114 $2) $3)) ((%114 $2) ((%89 ((%28 $4) ((%149
       $0) $1))) $3)))))))))))))))))))) (\%150. (\%116. ((%151 (\%112.
       (\%93. (((%152 (%153 %144)) (\%97. (\%85. ((%154 (\%73. (\%155.
       (((%156 (%153 (%157 ($7 ((%114 $5) $2))))) (\%158. (\%159. (%153
       (((%160 ((%147 (%148 ((%149 $1) $0))) $7)) (%157 ((%149 (%161 $3))
       ($9 ((%114 $7) $4))))) (%157 ($9 ((%114 $7) $4)))))))) $0)))) $1))))
       $0)))) $0)))))`)
  val lhsWithLastSym_curried_def =
    DT([], [],
       `(%111 (\%124. (%69 (\%101. ((%75 ((%162 $1) $0)) (%142 ((%114 $1)
       $0)))))))`)
  val rule_terminals_def =
    DT(["DISK_THM"], [],
       `(%31 (\%73. (%32 (\%74. ((%163 (%164 ((%28 $1) $0))) (%165 (\%166.
       ((%167 $0) ((%18 (%168 $0)) ((%113 $0) $1))))))))))`)
  val rule_nonterminals_def =
    DT(["DISK_THM"], [],
       `(%31 (\%73. (%32 (\%74. ((%163 (%169 ((%28 $1) $0))) ((%170 (%161
       $1)) (%165 (\%171. ((%167 $0) ((%18 (%172 $0)) ((%113 $0)
       $1)))))))))))`)
  val is_word_def =
    DT([], [], `(%32 (\%173. ((%25 (%174 $0)) ((%175 %168) $0))))`)
  val rules_def =
    DT(["DISK_THM"], [],
       `(%69 (\%176. (%31 (\%177. ((%102 (%178 ((%66 $1) $0))) $1)))))`)
  val startSym_def =
    DT(["DISK_THM"], [],
       `(%69 (\%176. (%31 (\%177. ((%77 (%179 ((%66 $1) $0))) $0)))))`)
  val terminals_def =
    DT(["DISK_THM"], [],
       `(%69 (\%176. (%31 (\%177. ((%163 (%180 ((%66 $1) $0))) (%181 ((%182
       %164) (%183 $1))))))))`)
  val nonTerminals_def =
    DT(["DISK_THM"], [],
       `(%69 (\%176. (%31 (\%177. ((%163 (%184 ((%66 $1) $0))) ((%170 (%161
       $0)) (%181 ((%182 %169) (%183 $1)))))))))`)
  val nonTerminalsML_primitive_def =
    DT([], [],
       `((%185 %186) ((%187 (%188 (\%189. ((%18 (%190 $0)) (%32 (\%74. (%31
       (\%73. (%31 (\%177. (%69 (\%85. (($4 ((%66 $0) $1)) ((%66 ((%89
       ((%28 $2) $3)) $0)) $1)))))))))))))) (\%191. (\%59. ((%192 (\%193.
       (\%177. (((%194 (%195 (%196 ((%149 (%161 $0)) %144)))) (\%97. (\%85.
       ((%197 (\%73. (\%74. (%195 ((%198 (%196 ((%199 %172) ((%200 ((%149
       (%161 $1)) %144)) $0)))) ($7 ((%66 $2) $4))))))) $1)))) $1))))
       $0)))))`)
  val terminalsML_primitive_def =
    DT([], [],
       `((%185 %201) ((%187 (%188 (\%189. ((%18 (%190 $0)) (%32 (\%74. (%31
       (\%73. (%31 (\%177. (%69 (\%85. (($4 ((%66 $0) $1)) ((%66 ((%89
       ((%28 $2) $3)) $0)) $1)))))))))))))) (\%202. (\%59. ((%192 (\%193.
       (\%177. (((%194 (%195 (%196 %144))) (\%97. (\%85. ((%197 (\%73.
       (\%74. (%195 ((%198 (%196 ((%199 %168) $0))) ($7 ((%66 $2) $4)))))))
       $1)))) $1)))) $0)))))`)
  val allSyms_def =
    DT([], [],
       `(%58 (\%203. ((%163 (%204 $0)) ((%198 (%184 $0)) (%180 $0)))))`)
  val allSymsML_def =
    DT([], [],
       `(%58 (\%203. ((%163 (%205 $0)) ((%198 (%186 $0)) (%201 $0)))))`)
  val derives_def =
    DT([], [],
       `(%58 (\%203. (%32 (\%206. (%32 (\%207. ((%25 (((%208 $2) $1) $0))
       (%10 (\%209. (%10 (\%210. (%10 (\%211. (%8 (\%212. ((%18 ((%75
       ((%200 ((%200 $3) ((%149 (%161 $0)) %144))) $2)) $5)) ((%18 ((%75
       ((%200 ((%200 $3) $1)) $2)) $4)) ((%213 ((%28 $0) $1)) (%178
       $6)))))))))))))))))))`)
  val lderives_def =
    DT([], [],
       `(%58 (\%203. (%32 (\%206. (%32 (\%207. ((%25 (((%214 $2) $1) $0))
       (%10 (\%209. (%10 (\%210. (%10 (\%211. (%8 (\%212. ((%18 ((%75
       ((%200 ((%200 $3) ((%149 (%161 $0)) %144))) $2)) $5)) ((%18 ((%175
       %168) $3)) ((%18 ((%75 ((%200 ((%200 $3) $1)) $2)) $4)) ((%213 ((%28
       $0) $1)) (%178 $6))))))))))))))))))))`)
  val rderives_def =
    DT([], [],
       `(%58 (\%203. (%32 (\%206. (%32 (\%207. ((%25 (((%215 $2) $1) $0))
       (%10 (\%209. (%10 (\%210. (%10 (\%211. (%8 (\%212. ((%18 ((%75
       ((%200 ((%200 $3) ((%149 (%161 $0)) %144))) $2)) $5)) ((%18 ((%175
       %168) $2)) ((%18 ((%75 ((%200 ((%200 $3) $1)) $2)) $4)) ((%213 ((%28
       $0) $1)) (%178 $6))))))))))))))))))))`)
  val gaw_def =
    DT([], [],
       `(%58 (\%203. (%111 (\%171. ((%25 ((%216 $1) $0)) (%10 (\%173. ((%18
       (((%217 (%208 $2)) ((%149 $1) %144)) $0)) ((%175 %168) $0)))))))))`)
  val sforms_def =
    DT([], [],
       `(%58 (\%203. ((%218 (%219 $0)) (%220 (\%221. ((%222 $0) (((%217
       (%208 $1)) ((%149 (%161 (%179 $1))) %144)) $0)))))))`)
  val language_def =
    DT([], [],
       `(%58 (\%203. ((%218 (%223 $0)) (%220 (\%221. ((%222 $0) ((%18
       (((%217 (%208 $1)) ((%149 (%161 (%179 $1))) %144)) $0)) ((%175 %168)
       $0))))))))`)
  val llanguage_def =
    DT([], [],
       `(%58 (\%203. ((%218 (%224 $0)) (%220 (\%221. ((%222 $0) ((%18
       (((%217 (%214 $1)) ((%149 (%161 (%179 $1))) %144)) $0)) ((%175 %168)
       $0))))))))`)
  val rlanguage_def =
    DT([], [],
       `(%58 (\%203. ((%218 (%225 $0)) (%220 (\%221. ((%222 $0) ((%18
       (((%217 (%215 $1)) ((%149 (%161 (%179 $1))) %144)) $0)) ((%175 %168)
       $0))))))))`)
  val is_null_def =
    DT([], [],
       `(%58 (\%203. (%32 (\%74. ((%25 ((%226 $1) $0)) (%32 (\%173. ((%6
       (((%217 (%208 $2)) $1) $0)) ((%6 (%174 $0)) ((%75 $0)
       %144))))))))))`)
  val numTmnls_def =
    DT(["DISK_THM"], [],
       `((%18 ((%35 (%227 %144)) %14)) (%111 (\%228. (%32 (\%229. ((%35
       (%227 ((%149 $1) $0))) (((%230 (%168 $1)) ((%37 (%38 (%39 %40)))
       (%227 $0))) (%227 $0))))))))`)
  val nullable_def =
    DT([], [],
       `(%58 (\%203. (%32 (\%231. ((%25 ((%232 $1) $0)) (((%217 (%208 $1))
       $0) %144))))))`)
  val nr_defn_tupled_AUX_def =
    DT([], [],
       `(%233 (\%234. ((%235 (%236 $0)) ((%237 $0) (\%238. (\%239. ((%240
       (\%203. (\%241. ((%242 (\%243. (\%244. (((%245 (%246 %247)) (\%248.
       (\%249. (((%250 (\%251. (((%245 (%246 %252)) (\%253. (\%254. (%246
       ((%18 ($10 ((%255 $8) ((%256 $6) ((%149 (%257 $2)) %144))))) ($10
       ((%255 $8) ((%256 $6) ((%149 $1) $0))))))))) $1))) (\%258. (((%245
       (%246 (%10 (\%74. (((%259 ((%18 ((%213 ((%28 $1) $0)) (%178 $7)))
       ((%18 (((%217 (%208 $7)) $0) %144)) ((%163 ((%260 (%196 $0)) (%196
       ((%200 $5) ((%149 (%161 $1)) %144))))) %261)))) ($9 ((%255 $7)
       ((%256 ((%200 $5) ((%149 (%161 $1)) %144))) $0)))) %252))))) (\%262.
       (\%263. (%246 ((%18 ($10 ((%255 $8) ((%256 $6) ((%149 (%161 $2))
       %144))))) ($10 ((%255 $8) ((%256 $6) ((%149 $1) $0))))))))) $1)))
       $1)))) $0)))) $0)))) $0)))))))`)
  val nr_defn_tupled_primitive_def =
    DT([], [],
       `((%235 %264) (%236 (%265 (\%234. ((%18 (%266 $0)) ((%18 (%32
       (\%267. (%58 (\%203. (%31 (\%258. (%32 (\%74. ((%6 ((%18 ((%213
       ((%28 $1) $0)) (%178 $2))) ((%18 (((%217 (%208 $2)) $0) %144))
       ((%163 ((%260 (%196 $0)) (%196 ((%200 $3) ((%149 (%161 $1))
       %144))))) %261)))) (($4 ((%255 $2) ((%256 ((%200 $3) ((%149 (%161
       $1)) %144))) $0))) ((%255 $2) ((%256 $3) ((%149 (%161 $1))
       %144)))))))))))))) ((%18 (%32 (\%268. (%111 (\%269. (%31 (\%270.
       (%32 (\%267. (%58 (\%203. ((%6 ((((%271 (%236 $5)) $5) ((%255 $0)
       ((%256 $1) ((%149 (%161 $2)) ((%149 $3) $4))))) ((%255 $0) ((%256
       $1) ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1) ((%149 (%161 $2))
       %144)))) ((%255 $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3)
       $4))))))))))))))))) ((%18 (%32 (\%268. (%111 (\%269. (%31 (\%270.
       (%32 (\%267. (%58 (\%203. ((%6 ((%236 $5) ((%255 $0) ((%256 $1)
       ((%149 (%161 $2)) %144))))) (($5 ((%255 $0) ((%256 $1) ((%149 $3)
       $4)))) ((%255 $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3)
       $4))))))))))))))))) ((%18 (%32 (\%272. (%111 (\%273. (%31 (\%274.
       (%32 (\%267. (%58 (\%203. ((%6 ((%236 $5) ((%255 $0) ((%256 $1)
       ((%149 (%257 $2)) %144))))) (($5 ((%255 $0) ((%256 $1) ((%149 $3)
       $4)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3)
       $4))))))))))))))))) (%32 (\%272. (%111 (\%273. (%31 (\%274. (%32
       (\%267. (%58 (\%203. ((%6 ((((%271 (%236 $5)) $5) ((%255 $0) ((%256
       $1) ((%149 (%257 $2)) ((%149 $3) $4))))) ((%255 $0) ((%256 $1)
       ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1) ((%149 (%257 $2))
       %144)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3)
       $4)))))))))))))))))))))))))`)
  val nr_defn_curried_def =
    DT([], [],
       `(%58 (\%275. (%32 (\%276. (%32 (\%277. ((%25 (((%278 $2) $1) $0))
       (%264 ((%255 $2) ((%256 $1) $0))))))))))`)
  val getRhs_tupled_primitive_def =
    DT([], [],
       `((%279 %280) ((%281 (%82 (\%83. ((%18 (%84 $0)) ((%18 (%32 (\%74.
       (%69 (\%85. (%31 (\%282. (%31 (\%73. ((%6 (%87 ((%77 $0) $1))) (($4
       ((%88 $0) $2)) ((%88 $0) ((%89 ((%28 $1) $3)) $2))))))))))))) (%32
       (\%74. (%69 (\%85. (%31 (\%282. (%31 (\%73. ((%6 ((%77 $0) $1)) (($4
       ((%88 $0) $2)) ((%88 $0) ((%89 ((%28 $1) $3)) $2)))))))))))))))))
       (\%283. (\%91. ((%284 (\%73. (\%93. (((%118 (%119 %120)) (\%97.
       (\%85. ((%121 (\%282. (\%74. (%119 (((%122 ((%77 $5) $1)) ((%285
       ((%123 $0) %120)) ($7 ((%88 $5) $2)))) ($7 ((%88 $5) $2)))))))
       $1)))) $0)))) $0)))))`)
  val getRhs_curried_def =
    DT([], [],
       `(%31 (\%100. (%69 (\%101. ((%125 ((%286 $1) $0)) (%280 ((%88 $1)
       $0)))))))`)
  val derivesNull_def =
    DT(["DISK_THM"], [],
       `((%18 (%58 (\%203. (%31 (\%251. ((%25 ((%287 $1) (%257 $0)))
       %247)))))) (%58 (\%203. (%31 (\%258. ((%25 ((%287 $1) (%161 $0)))
       ((%213 ((%28 $0) %144)) (%178 $1))))))))`)
  val numNonTmnls_primitive_def =
    DT([], [],
       `((%288 %289) ((%290 (%291 (\%292. ((%18 (%293 $0)) (%32 (\%74. (%31
       (\%73. (%69 (\%85. (($3 $0) ((%89 ((%28 $1) $2)) $0))))))))))))
       (\%294. (\%295. (((%296 (%297 %14)) (\%298. (\%85. ((%299 (\%73.
       (\%74. (%297 ((%37 ((%37 (%38 (%39 %40))) (%300 ((%199 %172) $0))))
       ($5 $2)))))) $1)))) $0)))))`)
  val nullableList_tupled_AUX_def =
    DT([], [],
       `(%233 (\%234. ((%235 (%301 $0)) ((%237 $0) (\%302. (\%303. ((%240
       (\%203. (\%304. ((%242 (\%267. (\%305. (((%245 (%246 %247)) (\%306.
       (\%155. (((%250 (\%251. (((%245 (%246 %252)) (\%307. (\%308. (%246
       ((%18 ($10 ((%255 $8) ((%256 $6) ((%149 (%257 $2)) %144))))) ($10
       ((%255 $8) ((%256 $6) ((%149 $1) $0))))))))) $1))) (\%309. (((%245
       (%246 (((%259 ((%113 (%161 $0)) $4)) %252) ((%310 (\%311. ($9 ((%255
       $7) ((%256 ((%149 (%161 $1)) $5)) $0))))) ((%286 $0) (%178 $6))))))
       (\%312. (\%313. (%246 ((%18 ($10 ((%255 $8) ((%256 $6) ((%149 (%161
       $2)) %144))))) ($10 ((%255 $8) ((%256 $6) ((%149 $1) $0)))))))))
       $1))) $1)))) $0)))) $0)))) $0)))))))`)
  val nullableList_tupled_primitive_def =
    DT([], [],
       `((%235 %314) (%301 (%265 (\%234. ((%18 (%266 $0)) ((%18 (%58
       (\%203. (%32 (\%267. (%31 (\%309. (%32 (\%311. ((%6 ((%18 (%87
       ((%113 (%161 $1)) $2))) ((%315 $0) ((%286 $1) (%178 $3))))) (($4
       ((%255 $3) ((%256 ((%149 (%161 $1)) $2)) $0))) ((%255 $3) ((%256 $2)
       ((%149 (%161 $1)) %144)))))))))))))) ((%18 (%32 (\%316. (%111
       (\%317. (%31 (\%274. (%32 (\%267. (%58 (\%203. ((%6 ((((%271 (%301
       $5)) $5) ((%255 $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3) $4)))))
       ((%255 $0) ((%256 $1) ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1)
       ((%149 (%161 $2)) %144)))) ((%255 $0) ((%256 $1) ((%149 (%161 $2))
       ((%149 $3) $4))))))))))))))))) ((%18 (%32 (\%316. (%111 (\%317. (%31
       (\%274. (%32 (\%267. (%58 (\%203. ((%6 ((%301 $5) ((%255 $0) ((%256
       $1) ((%149 (%161 $2)) %144))))) (($5 ((%255 $0) ((%256 $1) ((%149
       $3) $4)))) ((%255 $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3)
       $4))))))))))))))))) ((%18 (%32 (\%318. (%111 (\%319. (%31 (\%320.
       (%32 (\%267. (%58 (\%203. ((%6 ((%301 $5) ((%255 $0) ((%256 $1)
       ((%149 (%257 $2)) %144))))) (($5 ((%255 $0) ((%256 $1) ((%149 $3)
       $4)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3)
       $4))))))))))))))))) (%32 (\%318. (%111 (\%319. (%31 (\%320. (%32
       (\%267. (%58 (\%203. ((%6 ((((%271 (%301 $5)) $5) ((%255 $0) ((%256
       $1) ((%149 (%257 $2)) ((%149 $3) $4))))) ((%255 $0) ((%256 $1)
       ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1) ((%149 (%257 $2))
       %144)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3)
       $4)))))))))))))))))))))))))`)
  val nullableList_curried_def =
    DT([], [],
       `(%58 (\%275. (%32 (\%276. (%32 (\%277. ((%25 (((%321 $2) $1) $0))
       (%314 ((%255 $2) ((%256 $1) $0))))))))))`)
  val lhsWithNullSfx_tupled_primitive_def =
    DT([], [],
       `((%322 %323) ((%324 (%325 (\%326. ((%18 (%327 $0)) ((%18 (%31
       (\%73. (%328 (\%329. (%32 (\%330. (%58 (\%203. ((%6 (%87 ((%232 $0)
       $1))) (($4 ((%331 $0) $2)) ((%331 $0) ((%137 ((%15 $3) $1))
       $2))))))))))))) (%31 (\%73. (%328 (\%329. (%32 (\%330. (%58 (\%203.
       ((%6 ((%232 $0) $1)) (($4 ((%331 $0) $2)) ((%331 $0) ((%137 ((%15
       $3) $1)) $2))))))))))))))))) (\%332. (\%333. ((%334 (\%203. (\%335.
       (((%336 (%119 %120)) (\%337. (\%329. ((%338 (\%73. (\%330. (%119
       (((%122 ((%232 $5) $0)) ((%123 ((%149 (%161 $1)) %144)) ($7 ((%331
       $5) $2)))) ($7 ((%331 $5) $2))))))) $1)))) $0)))) $0)))))`)
  val lhsWithNullSfx_curried_def =
    DT([], [],
       `(%58 (\%275. (%328 (\%339. ((%125 ((%340 $1) $0)) (%323 ((%331 $1)
       $0)))))))`)
  val sfxNotNull_tupled_primitive_def =
    DT([], [],
       `((%341 %342) ((%343 (%344 (\%345. ((%18 (%346 $0)) ((%18 (%347
       (\%348. (%349 (\%350. (%32 (\%330. (%58 (\%203. ((%6 (%87 (%87
       ((%232 $0) $1)))) (($4 ((%351 $0) $2)) ((%351 $0) ((%352 ((%353 $3)
       $1)) $2))))))))))))) (%347 (\%348. (%349 (\%350. (%32 (\%330. (%58
       (\%203. ((%6 (%87 ((%232 $0) $1))) (($4 ((%351 $0) $2)) ((%351 $0)
       ((%352 ((%353 $3) $1)) $2))))))))))))))))) (\%354. (\%355. ((%356
       (\%203. (\%357. (((%358 (%119 %120)) (\%359. (\%350. ((%360 (\%348.
       (\%330. (%119 (((%122 (%87 ((%232 $5) $0))) ((%123 $0) ($7 ((%351
       $5) $2)))) ($7 ((%351 $5) $2))))))) $1)))) $0)))) $0)))))`)
  val sfxNotNull_curried_def =
    DT([], [],
       `(%58 (\%275. (%349 (\%361. ((%125 ((%362 $1) $0)) (%342 ((%351 $1)
       $0)))))))`)
  val datatype_rule = DT(["DISK_THM"], [], `(%363 (%364 %28))`)
  val rule_11 =
    DT(["DISK_THM"], [],
       `(%31 (\%9. (%32 (\%11. (%31 (\%365. (%32 (\%366. ((%25 ((%21 ((%28
       $3) $2)) ((%28 $1) $0))) ((%18 ((%77 $3) $1)) ((%75 $2)
       $0)))))))))))`)
  val rule_case_cong =
    DT(["DISK_THM"], [],
       `(%19 (\%367. (%19 (\%368. (%29 (\%30. ((%6 ((%18 ((%21 $2) $1))
       (%31 (\%9. (%32 (\%11. ((%6 ((%21 $3) ((%28 $1) $0))) ((%33 (($2 $1)
       $0)) ((%369 $1) $0))))))))) ((%33 ((%34 $0) $2)) ((%34 %369)
       $1)))))))))`)
  val rule_nchotomy =
    DT(["DISK_THM"], [],
       `(%19 (\%370. (%8 (\%177. (%10 (\%371. ((%21 $2) ((%28 $1)
       $0))))))))`)
  val rule_Axiom =
    DT(["DISK_THM"], [],
       `(%29 (\%30. (%372 (\%373. (%31 (\%9. (%32 (\%11. ((%33 ($2 ((%28
       $1) $0))) (($3 $1) $0))))))))))`)
  val rule_induction =
    DT(["DISK_THM"], [],
       `(%374 (\%375. ((%6 (%31 (\%177. (%32 (\%371. ($2 ((%28 $1)
       $0))))))) (%19 (\%370. ($1 $0))))))`)
  val datatype_grammar = DT(["DISK_THM"], [], `(%363 (%376 %66))`)
  val grammar_11 =
    DT(["DISK_THM"], [],
       `(%69 (\%52. (%31 (\%53. (%69 (\%377. (%31 (\%378. ((%25 ((%60 ((%66
       $3) $2)) ((%66 $1) $0))) ((%18 ((%102 $3) $1)) ((%77 $2)
       $0)))))))))))`)
  val grammar_case_cong =
    DT(["DISK_THM"], [],
       `(%58 (\%379. (%58 (\%380. (%67 (\%68. ((%6 ((%18 ((%60 $2) $1))
       (%69 (\%52. (%31 (\%53. ((%6 ((%60 $3) ((%66 $1) $0))) ((%33 (($2
       $1) $0)) ((%381 $1) $0))))))))) ((%33 ((%70 $0) $2)) ((%70 %381)
       $1)))))))))`)
  val grammar_nchotomy =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%51 (\%382. (%8 (\%177. ((%60 $2) ((%66 $1)
       $0))))))))`)
  val grammar_Axiom =
    DT(["DISK_THM"], [],
       `(%67 (\%68. (%383 (\%384. (%69 (\%52. (%31 (\%53. ((%33 ($2 ((%66
       $1) $0))) (($3 $1) $0))))))))))`)
  val grammar_induction =
    DT(["DISK_THM"], [],
       `(%385 (\%386. ((%6 (%69 (\%382. (%31 (\%177. ($2 ((%66 $1)
       $0))))))) (%58 (\%203. ($1 $0))))))`)
  val getRules_ind =
    DT(["DISK_THM"], [],
       `(%387 (\%388. ((%6 ((%18 (%31 (\%86. (($1 $0) %96)))) (%31 (\%86.
       (%31 (\%73. (%32 (\%74. (%69 (\%85. ((%6 ((%18 ((%6 (%87 ((%77 $3)
       $2))) (($4 $3) $0))) ((%6 ((%77 $3) $2)) (($4 $3) $0)))) (($4 $3)
       ((%89 ((%28 $2) $1)) $0))))))))))))) (%31 (\%389. (%69 (\%93. (($2
       $1) $0))))))))`)
  val getRules_def =
    DT(["DISK_THM"], [],
       `((%18 ((%102 ((%103 %86) %96)) %96)) ((%102 ((%103 %86) ((%89 ((%28
       %73) %74)) %85))) (((%99 ((%77 %86) %73)) ((%89 ((%28 %73) %74))
       ((%103 %86) %85))) ((%103 %86) %85))))`)
  val rhsWithSym_ind =
    DT(["DISK_THM"], [],
       `(%390 (\%391. ((%6 ((%18 (%111 (\%112. (($1 $0) %96)))) (%111
       (\%112. (%31 (\%73. (%32 (\%74. (%69 (\%110. ((%6 ((%18 ((%6 (%87
       ((%113 $3) $1))) (($4 $3) $0))) ((%6 ((%113 $3) $1)) (($4 $3) $0))))
       (($4 $3) ((%89 ((%28 $2) $1)) $0))))))))))))) (%111 (\%392. (%69
       (\%93. (($2 $1) $0))))))))`)
  val rhsWithSym_def =
    DT(["DISK_THM"], [],
       `((%18 ((%125 ((%126 %112) %96)) %120)) ((%125 ((%126 %112) ((%89
       ((%28 %73) %74)) %110))) (((%122 ((%113 %112) %74)) ((%123 %74)
       ((%126 %112) %110))) ((%126 %112) %110))))`)
  val rulesWithSymInRhs_ind =
    DT(["DISK_THM"], [],
       `(%390 (\%391. ((%6 ((%18 (%111 (\%112. (($1 $0) %96)))) (%111
       (\%112. (%31 (\%73. (%32 (\%74. (%69 (\%110. ((%6 ((%18 ((%6 (%87
       ((%113 $3) $1))) (($4 $3) $0))) ((%6 ((%113 $3) $1)) (($4 $3) $0))))
       (($4 $3) ((%89 ((%28 $2) $1)) $0))))))))))))) (%111 (\%392. (%69
       (\%93. (($2 $1) $0))))))))`)
  val rulesWithSymInRhs_def =
    DT(["DISK_THM"], [],
       `((%18 ((%139 ((%140 %112) %96)) %134)) ((%139 ((%140 %112) ((%89
       ((%28 %73) %74)) %110))) (((%136 ((%113 %112) %74)) ((%137 ((%15
       %73) ((%138 %112) %74))) ((%140 %112) %110))) ((%140 %112)
       %110))))`)
  val lhsWithLastSym_ind =
    DT(["DISK_THM"], [],
       `(%390 (\%391. ((%6 ((%18 (%111 (\%112. (($1 $0) %96)))) ((%18 (%111
       (\%112. (%31 (\%73. (%69 (\%85. ((%6 (($3 $2) $0)) (($3 $2) ((%89
       ((%28 $1) %144)) $0)))))))))) (%111 (\%112. (%31 (\%73. (%111
       (\%146. (%32 (\%145. (%69 (\%85. ((%6 ((%18 ((%6 (%87 ((%147 (%148
       ((%149 $2) $1))) $4))) (($5 $4) $0))) ((%6 ((%147 (%148 ((%149 $2)
       $1))) $4)) (($5 $4) $0)))) (($5 $4) ((%89 ((%28 $3) ((%149 $2) $1)))
       $0)))))))))))))))) (%111 (\%392. (%69 (\%93. (($2 $1) $0))))))))`)
  val lhsWithLastSym_def =
    DT(["DISK_THM"], [],
       `((%18 ((%75 ((%162 %112) %96)) %144)) ((%18 ((%75 ((%162 %112)
       ((%89 ((%28 %73) %144)) %85))) (%157 ((%162 %112) %85)))) ((%75
       ((%162 %112) ((%89 ((%28 %73) ((%149 %146) %145))) %85))) (((%160
       ((%147 (%148 ((%149 %146) %145))) %112)) (%157 ((%149 (%161 %73))
       ((%162 %112) %85)))) (%157 ((%162 %112) %85))))))`)
  val lwls_r1 =
    DT(["DISK_THM"], [],
       `((%6 (%87 ((%75 ((%162 %112) ((%89 ((%28 %177) %371)) %85)))
       %144))) ((%393 (%87 ((%75 ((%162 %112) ((%89 ((%28 %177) %371))
       %96))) %144))) (%87 ((%75 ((%162 %112) %85)) %144))))`)
  val notNullLhsLastSym =
    DT(["DISK_THM", "MK_THM"], [],
       `(%111 (\%112. (%69 (\%85. ((%6 (%87 ((%75 ((%162 $1) $0)) %144)))
       (%8 (\%73. (%10 (\%394. ((%213 ((%28 $1) ((%200 $0) ((%149 $3)
       %144)))) $2))))))))))`)
  val nonTerminalsML_ind =
    DT(["DISK_THM"], [],
       `(%385 (\%386. ((%6 ((%18 (%31 (\%177. ($1 ((%66 %96) $0))))) (%31
       (\%73. (%32 (\%74. (%69 (\%85. (%31 (\%177. ((%6 ($4 ((%66 $1) $0)))
       ($4 ((%66 ((%89 ((%28 $3) $2)) $1)) $0))))))))))))) (%58 (\%395. ($1
       $0))))))`)
  val nonTerminalsML_def =
    DT(["DISK_THM"], [],
       `((%18 ((%163 (%186 ((%66 %96) %177))) (%196 ((%149 (%161 %177))
       %144)))) ((%163 (%186 ((%66 ((%89 ((%28 %73) %74)) %85)) %177)))
       ((%198 (%196 ((%199 %172) ((%200 ((%149 (%161 %73)) %144)) %74))))
       (%186 ((%66 %85) %177)))))`)
  val terminalsML_ind =
    DT(["DISK_THM"], [],
       `(%385 (\%386. ((%6 ((%18 (%31 (\%177. ($1 ((%66 %96) $0))))) (%31
       (\%73. (%32 (\%74. (%69 (\%85. (%31 (\%177. ((%6 ($4 ((%66 $1) $0)))
       ($4 ((%66 ((%89 ((%28 $3) $2)) $1)) $0))))))))))))) (%58 (\%395. ($1
       $0))))))`)
  val terminalsML_def =
    DT(["DISK_THM"], [],
       `((%18 ((%163 (%201 ((%66 %96) %177))) (%196 %144))) ((%163 (%201
       ((%66 ((%89 ((%28 %73) %74)) %85)) %177))) ((%198 (%196 ((%199 %168)
       %74))) (%201 ((%66 %85) %177)))))`)
  val nonTerminalsEq =
    DT(["DISK_THM"], [], `((%163 (%184 %203)) (%186 %203))`)
  val terminalsEq =
    DT(["DISK_THM"], [], `((%163 (%180 %203)) (%201 %203))`)
  val allSymsEq = DT(["DISK_THM"], [], `((%163 (%204 %203)) (%205 %203))`)
  val derives_same_append_left =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%32 (\%396. (%32 (\%397. ((%6 (((%208 $2) $1) $0))
       (%32 (\%398. (((%208 $3) ((%200 $0) $2)) ((%200 $0) $1)))))))))))`)
  val derives_same_append_right =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%32 (\%396. (%32 (\%397. ((%6 (((%208 $2) $1) $0))
       (%32 (\%398. (((%208 $3) ((%200 $2) $0)) ((%200 $1) $0)))))))))))`)
  val rtc_derives_same_append_left =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%208 %203)) $1) $0)) (%32
       (\%398. (((%217 (%208 %203)) ((%200 $0) $2)) ((%200 $0)
       $1)))))))))`)
  val b1 =
    DT(["DISK_THM"], [],
       `(%32 (\%399. (%87 (((%217 (%208 %203)) %144) ((%149 %400) $0)))))`)
  val rtc_derives_same_append_right =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%208 %203)) $1) $0)) (%32
       (\%398. (((%217 (%208 %203)) ((%200 $2) $0)) ((%200 $1)
       $0)))))))))`)
  val derives_append =
    DT(["DISK_THM"], [],
       `((%6 ((%18 (((%217 (%208 %203)) %401) %402)) (((%217 (%208 %203))
       %403) %404))) (((%217 (%208 %203)) ((%200 %401) %403)) ((%200 %402)
       %404)))`)
  val res1 =
    DT(["DISK_THM"], [],
       `(%31 (\%212. (%32 (\%211. (%58 (\%203. ((%6 ((%213 ((%28 $2) $1))
       (%178 $0))) (((%208 $0) ((%149 (%161 $2)) %144)) $1))))))))`)
  val res2 =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%32 (\%311. (%32 (\%405. ((%6 (((%208 $2) $1) $0))
       (%32 (\%406. ((%6 (((%208 $3) $1) $0)) (((%217 (%208 $3)) $2)
       $0)))))))))))`)
  val res3 =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%32 (\%311. (%32 (\%405. ((%6 (((%208 $2) $1) $0))
       (%32 (\%406. ((%6 (((%217 (%208 $3)) $1) $0)) (((%217 (%208 $3)) $2)
       $0)))))))))))`)
  val slres =
    DT(["DISK_THM"], [],
       `((%6 ((%75 ((%200 ((%200 %209) ((%149 (%161 %212)) %144))) %210))
       ((%149 (%161 %177)) %144))) ((%77 %212) %177))`)
  val slres2 =
    DT(["DISK_THM"], [],
       `((%6 ((%75 ((%200 ((%200 %209) ((%149 (%161 %212)) %144))) %210))
       ((%149 (%161 %177)) %144))) ((%18 ((%75 %209) %144)) ((%75 %210)
       %144)))`)
  val rgr_r8 =
    DT(["DISK_THM"], [],
       `((%6 ((%75 %74) ((%200 ((%200 %407) ((%149 %112) %144))) %408)))
       ((%6 (((%208 %203) ((%149 (%161 %73)) %144)) %74)) (%10 (\%311. (%10
       (\%405. (((%208 %203) ((%149 (%161 %73)) %144)) ((%200 ((%200 $1)
       ((%149 %112) %144))) $0))))))))`)
  val sub_result =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%32 (\%409. ((%6 ((%175 (%216 $1)) $0)) (%10 (\%173.
       ((%18 (((%217 (%208 $2)) $1) $0)) ((%175 %168) $0)))))))))`)
  val key_result =
    DT(["DISK_THM"], [],
       `((%6 ((%18 ((%175 (%216 %203)) %397)) (((%208 %203) %396) %397)))
       ((%175 (%216 %203)) %396))`)
  val sub_result_rev =
    DT(["DISK_THM"], [],
       `(%32 (\%409. ((%6 (%10 (\%173. ((%18 (((%217 (%208 %203)) $1) $0))
       ((%175 %168) $0))))) ((%175 (%216 %203)) $0))))`)
  val term_syms_gen_words =
    DT(["DISK_THM"], [],
       `((%6 ((%175 %168) %173)) ((%175 (%216 %203)) %173))`)
  val upgr_r7 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%410. ((%6 (((%217 (%208 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 %398) %411))) (%10 (\%412. (%10 (\%413. ((%6 ((%75
       $2) ((%200 $1) $0))) ((%18 (((%217 (%208 %203)) %398) $1)) (((%217
       (%208 %203)) %411) $0)))))))))))))`)
  val lupgr_r7 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%410. ((%6 (((%217 (%214 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 %398) %411))) (%10 (\%412. (%10 (\%413. ((%6 ((%75
       $2) ((%200 $1) $0))) ((%18 (((%217 (%214 %203)) %398) $1)) (((%217
       (%214 %203)) %411) $0)))))))))))))`)
  val upgr_r11 =
    DT(["DISK_THM"], [],
       `((%6 (((%208 %203) ((%149 (%161 %212)) %144)) ((%149 (%161 %414))
       %144))) ((%213 ((%28 %212) ((%149 (%161 %414)) %144))) (%178
       %203)))`)
  val lupgr_r11 =
    DT(["DISK_THM"], [],
       `((%6 (((%214 %203) ((%149 (%161 %212)) %144)) ((%149 (%161 %414))
       %144))) ((%213 ((%28 %212) ((%149 (%161 %414)) %144))) (%178
       %203)))`)
  val upgr_r15 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%208 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 ((%200 %209) %415)) %210))) ((%6 ((%213 ((%28 %212)
       %415)) (%178 %203))) (((%217 (%208 %203)) ((%200 ((%200 %209) ((%149
       (%161 %212)) %144))) %210)) $0))))))))`)
  val rtc_r1 =
    DT(["DISK_THM"], [],
       `((%6 (((%217 (%208 %203)) %209) %210)) ((%6 (%87 ((%75 %209)
       %210))) (%10 (\%416. ((%18 (((%208 %203) %209) $0)) (((%217 (%208
       %203)) $0) %210))))))`)
  val upgr_r18 =
    DT(["DISK_THM"], [],
       `((%6 (((%208 %203) %417) %418)) (%10 (\%394. (%10 (\%330. ((%18
       ((%75 %418) ((%200 $1) $0))) (((%208 %203) %417) $1)))))))`)
  val lemma2 =
    DT(["DISK_THM"], [],
       `(%32 (\%209. (%32 (\%210. (%347 (\%419. (%420 (\%421. ((%6 (((%208
       %203) ((%200 $3) $2)) %417)) ((%393 (%10 (\%422. ((%18 (((%208 %203)
       $4) $0)) ((%75 %417) ((%200 $0) $3)))))) (%10 (\%423. ((%18 (((%208
       %203) $3) $0)) ((%75 %417) ((%200 $4) $0)))))))))))))))`)
  val llemma2 =
    DT(["DISK_THM"], [],
       `(%32 (\%209. (%32 (\%210. (%347 (\%419. (%420 (\%421. ((%6 (((%214
       %203) ((%200 $3) $2)) %417)) ((%393 (%10 (\%422. ((%18 (((%214 %203)
       $4) $0)) ((%75 %417) ((%200 $0) $3)))))) (%10 (\%423. ((%18 (((%214
       %203) $3) $0)) ((%75 %417) ((%200 $4) $0)))))))))))))))`)
  val upgr_r17 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%208 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 %398) %411))) (%10 (\%412. (%10 (\%413. ((%18 ((%75
       $2) ((%200 $1) $0))) ((%18 (((%217 (%208 %203)) %398) $1)) (((%217
       (%208 %203)) %411) $0)))))))))))))`)
  val lupgr_r17 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%214 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 %398) %411))) (%10 (\%412. (%10 (\%413. ((%18 ((%75
       $2) ((%200 $1) $0))) ((%18 (((%217 (%214 %203)) %398) $1)) (((%217
       (%214 %203)) %411) $0)))))))))))))`)
  val upgr_r19 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%208 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 ((%200 %398) %411)) %410))) (%10 (\%412. (%10
       (\%413. (%10 (\%424. ((%18 ((%75 $3) ((%200 ((%200 $2) $1)) $0)))
       ((%18 (((%217 (%208 %203)) %398) $2)) ((%18 (((%217 (%208 %203))
       %411) $1)) (((%217 (%208 %203)) %410) $0))))))))))))))))`)
  val lupgr_r19 =
    DT(["DISK_THM"], [],
       `(%32 (\%396. (%32 (\%397. ((%6 (((%217 (%214 %203)) $1) $0)) ((%6
       ((%75 $1) ((%200 ((%200 %398) %411)) %410))) (%10 (\%412. (%10
       (\%413. (%10 (\%424. ((%18 ((%75 $3) ((%200 ((%200 $2) $1)) $0)))
       ((%18 (((%217 (%214 %203)) %398) $2)) ((%18 (((%217 (%214 %203))
       %411) $1)) (((%217 (%214 %203)) %410) $0))))))))))))))))`)
  val slemma1_4 =
    DT(["DISK_THM"], [],
       `((%25 ((%425 (%161 %258)) (%184 %203))) (%10 (\%211. ((%393 ((%213
       ((%28 %258) $0)) (%178 %203))) (%8 (\%73. (%10 (\%426. (%10 (\%417.
       ((%393 ((%213 ((%28 $2) ((%200 ((%200 $1) ((%149 (%161 %258))
       %144))) $0))) (%178 %203))) ((%77 %258) (%179 %203)))))))))))))`)
  val slemma1_3 =
    DT(["DISK_THM"], [],
       `((%25 (%87 ((%425 (%161 %258)) (%184 %203)))) ((%18 (%87 (%10
       (\%211. ((%213 ((%28 %258) $0)) (%178 %203)))))) ((%18 (%87 (%8
       (\%73. (%10 (\%426. (%10 (\%417. ((%213 ((%28 $2) ((%200 ((%200 $1)
       ((%149 (%161 %258)) %144))) $0))) (%178 %203)))))))))) (%87 ((%77
       %258) (%179 %203))))))`)
  val emptySetList =
    DT(["DISK_THM"], [],
       `((%25 ((%427 %428) (%429 %430))) ((%431 %430) %432))`)
  val finiteNtsList =
    DT(["DISK_THM"], [],
       `(%374 (\%433. ((%6 (%434 $0)) (%58 (\%203. ((%6 ((%435 $1) (%183
       (%178 $0)))) (%436 (%184 $0))))))))`)
  val rt1 =
    DT(["DISK_THM"], [],
       `(%111 (\%437. (%19 (\%370. ((%6 ((%425 $1) (%164 $0))) (%87 (%172
       $1)))))))`)
  val rt2 =
    DT(["DISK_THM"], [],
       `(%111 (\%437. ((%6 (%87 (%172 $0))) (%438 (\%370. ((%425 $1) (%164
       $0)))))))`)
  val rt =
    DT(["DISK_THM"], [],
       `(%111 (\%437. ((%25 (%438 (\%370. ((%425 $1) (%164 $0))))) (%87
       (%172 $0)))))`)
  val ntsNotInTmnls1 =
    DT(["DISK_THM"], [],
       `(%111 (\%171. ((%6 (%172 $0)) (%87 ((%425 $0) (%180 %203))))))`)
  val ntsNotInTmnls =
    DT(["DISK_THM"], [],
       `(%31 (\%258. (%87 ((%425 (%161 $0)) (%180 %203)))))`)
  val rnt1 =
    DT(["DISK_THM"], [],
       `(%111 (\%437. (%19 (\%370. ((%6 ((%425 $1) (%169 $0))) (%87 (%168
       $1)))))))`)
  val rnt2 =
    DT(["DISK_THM"], [],
       `(%111 (\%437. ((%6 (%87 (%168 $0))) (%438 (\%370. ((%425 $1) (%169
       $0)))))))`)
  val rnt =
    DT(["DISK_THM"], [],
       `(%111 (\%437. ((%25 (%438 (\%370. ((%425 $1) (%169 $0))))) (%87
       (%168 $0)))))`)
  val tsNotInNonTmnls =
    DT(["DISK_THM"], [],
       `(%31 (\%251. (%87 ((%425 (%257 $0)) (%184 %203)))))`)
  val allNtSymsInGr =
    DT(["DISK_THM"], [],
       `(%31 (\%258. ((%25 ((%425 (%161 $0)) (%204 %203))) ((%393 (%10
       (\%211. ((%213 ((%28 $1) $0)) (%178 %203))))) ((%393 (%8 (\%73. (%10
       (\%426. (%10 (\%417. ((%213 ((%28 $2) ((%200 ((%200 $1) ((%149 (%161
       $3)) %144))) $0))) (%178 %203))))))))) ((%77 $0) (%179 %203)))))))`)
  val allTmSymsInGr =
    DT(["DISK_THM"], [],
       `(%31 (\%251. ((%25 ((%425 (%257 $0)) (%204 %203))) (%8 (\%73. (%10
       (\%426. (%10 (\%417. ((%213 ((%28 $2) ((%200 ((%200 $1) ((%149 (%257
       $3)) %144))) $0))) (%178 %203)))))))))))`)
  val symInGr =
    DT(["DISK_THM", "MK_THM"], [],
       `(%111 (\%112. (%58 (\%203. ((%6 (%87 ((%75 ((%162 $1) (%178 $0)))
       %144))) ((%425 $1) (%204 $0)))))))`)
  val finiteTerminals =
    DT(["DISK_THM"], [],
       `(%374 (\%433. ((%6 (%434 $0)) (%58 (\%203. ((%6 ((%435 $1) (%183
       (%178 $0)))) (%436 (%180 $0))))))))`)
  val finiteAllSyms =
    DT(["DISK_THM"], [],
       `(%374 (\%433. ((%6 (%434 $0)) (%58 (\%203. ((%6 ((%435 $1) (%183
       (%178 $0)))) (%436 (%204 $0))))))))`)
  val getRhs_ind =
    DT(["DISK_THM"], [],
       `(%387 (\%388. ((%6 ((%18 (%31 (\%73. (($1 $0) %96)))) (%31 (\%73.
       (%31 (\%282. (%32 (\%74. (%69 (\%85. ((%6 ((%18 ((%6 (%87 ((%77 $3)
       $2))) (($4 $3) $0))) ((%6 ((%77 $3) $2)) (($4 $3) $0)))) (($4 $3)
       ((%89 ((%28 $2) $1)) $0))))))))))))) (%31 (\%389. (%69 (\%93. (($2
       $1) $0))))))))`)
  val getRhs_def =
    DT(["DISK_THM"], [],
       `((%18 ((%125 ((%286 %73) %96)) %120)) ((%125 ((%286 %73) ((%89
       ((%28 %282) %74)) %85))) (((%122 ((%77 %73) %282)) ((%285 ((%123
       %74) %120)) ((%286 %73) %85))) ((%286 %73) %85))))`)
  val numNonTmnls_ind =
    DT(["DISK_THM"], [],
       `(%439 (\%440. ((%6 ((%18 ($0 %96)) (%31 (\%73. (%32 (\%74. (%69
       (\%85. ((%6 ($3 $0)) ($3 ((%89 ((%28 $2) $1)) $0))))))))))) (%69
       (\%193. ($1 $0))))))`)
  val numNonTmnls_def =
    DT(["DISK_THM"], [],
       `((%18 ((%35 (%289 %96)) %14)) ((%35 (%289 ((%89 ((%28 %73) %74))
       %85))) ((%37 ((%37 (%38 (%39 %40))) (%300 ((%199 %172) %74)))) (%289
       %85))))`)
  val getRhsDistrib =
    DT(["DISK_THM"], [],
       `(%69 (\%441. (%69 (\%442. ((%125 ((%286 %309) ((%443 $1) $0)))
       ((%285 ((%286 %309) $1)) ((%286 %309) $0)))))))`)
  val x_1 =
    DT(["DISK_THM"], [],
       `((%25 ((%315 %444) ((%286 %309) (%178 %203)))) (((%208 %203) ((%149
       (%161 %309)) %144)) %444))`)
  val notNullGetRhs_1 =
    DT(["DISK_THM"], [],
       `(%31 (\%258. (%58 (\%203. ((%6 (%87 ((%125 ((%286 $1) (%178 $0)))
       %120))) (%10 (\%74. ((%213 ((%28 $2) $0)) (%178 $1)))))))))`)
  val notNullGetRhs_2 =
    DT(["DISK_THM"], [],
       `((%6 (%10 (\%74. ((%213 ((%28 %258) $0)) (%178 %203))))) (%87
       ((%125 ((%286 %258) (%178 %203))) %120)))`)
  val notNullGetRhs =
    DT(["DISK_THM"], [],
       `((%25 (%10 (\%74. ((%213 ((%28 %258) $0)) (%178 %203))))) (%87
       ((%125 ((%286 %258) (%178 %203))) %120)))`)
  val ntsInGr =
    DT(["DISK_THM"], [],
       `(%31 (\%258. (%58 (\%203. ((%6 (%87 ((%125 ((%286 $1) (%178 $0)))
       %120))) ((%425 (%161 $1)) (%184 $0)))))))`)
  val nullableML =
    DT(["DISK_THM"], [],
       `((%18 ((%25 (((%321 %203) %267) %144)) %247)) ((%18 ((%25 (((%321
       %203) %267) ((%149 (%257 %251)) %144))) %252)) ((%18 ((%25 (((%321
       %203) %267) ((%149 (%161 %309)) %144))) (((%259 ((%113 (%161 %309))
       %267)) %252) ((%310 (\%311. (((%321 %203) ((%149 (%161 %309)) %267))
       $0))) ((%286 %309) (%178 %203)))))) ((%18 ((%25 (((%321 %203) %267)
       ((%149 (%161 %274)) ((%149 %317) %316)))) ((%18 (((%321 %203) %267)
       ((%149 (%161 %274)) %144))) (((%321 %203) %267) ((%149 %317)
       %316))))) ((%25 (((%321 %203) %267) ((%149 (%257 %320)) ((%149 %319)
       %318)))) ((%18 (((%321 %203) %267) ((%149 (%257 %320)) %144)))
       (((%321 %203) %267) ((%149 %319) %318))))))))`)
  val nullableML_ind =
    DT(["DISK_THM"], [],
       `(%445 (\%446. ((%6 ((%18 (%58 (\%203. (%32 (\%267. ((($2 $1) $0)
       %144)))))) ((%18 (%58 (\%203. (%32 (\%267. (%31 (\%251. ((($3 $2)
       $1) ((%149 (%257 $0)) %144))))))))) ((%18 (%58 (\%203. (%32 (\%267.
       (%31 (\%309. ((%6 (%32 (\%311. ((%6 ((%18 (%87 ((%113 (%161 $1))
       $2))) ((%315 $0) ((%286 $1) (%178 $3))))) ((($4 $3) ((%149 (%161
       $1)) $2)) $0))))) ((($3 $2) $1) ((%149 (%161 $0)) %144))))))))))
       ((%18 (%58 (\%203. (%32 (\%267. (%31 (\%274. (%111 (\%317. (%32
       (\%316. ((%6 ((%18 ((%6 (((%321 $4) $3) ((%149 (%161 $2)) %144)))
       ((($5 $4) $3) ((%149 $1) $0)))) ((%6 ((((%271 %314) (%265 (\%234.
       ((%18 (%266 $0)) ((%18 (%58 (\%203. (%32 (\%267. (%31 (\%309. (%32
       (\%311. ((%6 ((%18 (%87 ((%113 (%161 $1)) $2))) ((%315 $0) ((%286
       $1) (%178 $3))))) (($4 ((%255 $3) ((%256 ((%149 (%161 $1)) $2))
       $0))) ((%255 $3) ((%256 $2) ((%149 (%161 $1)) %144))))))))))))))
       ((%18 (%32 (\%316. (%111 (\%317. (%31 (\%274. (%32 (\%267. (%58
       (\%203. ((%6 ((((%271 (%301 $5)) $5) ((%255 $0) ((%256 $1) ((%149
       (%161 $2)) ((%149 $3) $4))))) ((%255 $0) ((%256 $1) ((%149 $3)
       $4))))) (($5 ((%255 $0) ((%256 $1) ((%149 (%161 $2)) %144)))) ((%255
       $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3) $4)))))))))))))))))
       ((%18 (%32 (\%316. (%111 (\%317. (%31 (\%274. (%32 (\%267. (%58
       (\%203. ((%6 ((%301 $5) ((%255 $0) ((%256 $1) ((%149 (%161 $2))
       %144))))) (($5 ((%255 $0) ((%256 $1) ((%149 $3) $4)))) ((%255 $0)
       ((%256 $1) ((%149 (%161 $2)) ((%149 $3) $4))))))))))))))))) ((%18
       (%32 (\%318. (%111 (\%319. (%31 (\%320. (%32 (\%267. (%58 (\%203.
       ((%6 ((%301 $5) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) %144)))))
       (($5 ((%255 $0) ((%256 $1) ((%149 $3) $4)))) ((%255 $0) ((%256 $1)
       ((%149 (%257 $2)) ((%149 $3) $4))))))))))))))))) (%32 (\%318. (%111
       (\%319. (%31 (\%320. (%32 (\%267. (%58 (\%203. ((%6 ((((%271 (%301
       $5)) $5) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3) $4)))))
       ((%255 $0) ((%256 $1) ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1)
       ((%149 (%257 $2)) %144)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2))
       ((%149 $3) $4)))))))))))))))))))))))) ((%255 $4) ((%256 $3) ((%149
       (%161 $2)) ((%149 $1) $0))))) ((%255 $4) ((%256 $3) ((%149 $1)
       $0))))) ((($5 $4) $3) ((%149 (%161 $2)) %144))))) ((($5 $4) $3)
       ((%149 (%161 $2)) ((%149 $1) $0))))))))))))))) (%58 (\%203. (%32
       (\%267. (%31 (\%320. (%111 (\%319. (%32 (\%318. ((%6 ((%18 ((%6
       (((%321 $4) $3) ((%149 (%257 $2)) %144))) ((($5 $4) $3) ((%149 $1)
       $0)))) ((%6 ((((%271 %314) (%265 (\%234. ((%18 (%266 $0)) ((%18 (%58
       (\%203. (%32 (\%267. (%31 (\%309. (%32 (\%311. ((%6 ((%18 (%87
       ((%113 (%161 $1)) $2))) ((%315 $0) ((%286 $1) (%178 $3))))) (($4
       ((%255 $3) ((%256 ((%149 (%161 $1)) $2)) $0))) ((%255 $3) ((%256 $2)
       ((%149 (%161 $1)) %144)))))))))))))) ((%18 (%32 (\%316. (%111
       (\%317. (%31 (\%274. (%32 (\%267. (%58 (\%203. ((%6 ((((%271 (%301
       $5)) $5) ((%255 $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3) $4)))))
       ((%255 $0) ((%256 $1) ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1)
       ((%149 (%161 $2)) %144)))) ((%255 $0) ((%256 $1) ((%149 (%161 $2))
       ((%149 $3) $4))))))))))))))))) ((%18 (%32 (\%316. (%111 (\%317. (%31
       (\%274. (%32 (\%267. (%58 (\%203. ((%6 ((%301 $5) ((%255 $0) ((%256
       $1) ((%149 (%161 $2)) %144))))) (($5 ((%255 $0) ((%256 $1) ((%149
       $3) $4)))) ((%255 $0) ((%256 $1) ((%149 (%161 $2)) ((%149 $3)
       $4))))))))))))))))) ((%18 (%32 (\%318. (%111 (\%319. (%31 (\%320.
       (%32 (\%267. (%58 (\%203. ((%6 ((%301 $5) ((%255 $0) ((%256 $1)
       ((%149 (%257 $2)) %144))))) (($5 ((%255 $0) ((%256 $1) ((%149 $3)
       $4)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3)
       $4))))))))))))))))) (%32 (\%318. (%111 (\%319. (%31 (\%320. (%32
       (\%267. (%58 (\%203. ((%6 ((((%271 (%301 $5)) $5) ((%255 $0) ((%256
       $1) ((%149 (%257 $2)) ((%149 $3) $4))))) ((%255 $0) ((%256 $1)
       ((%149 $3) $4))))) (($5 ((%255 $0) ((%256 $1) ((%149 (%257 $2))
       %144)))) ((%255 $0) ((%256 $1) ((%149 (%257 $2)) ((%149 $3)
       $4)))))))))))))))))))))))) ((%255 $4) ((%256 $3) ((%149 (%257 $2))
       ((%149 $1) $0))))) ((%255 $4) ((%256 $3) ((%149 $1) $0))))) ((($5
       $4) $3) ((%149 (%257 $2)) %144))))) ((($5 $4) $3) ((%149 (%257 $2))
       ((%149 $1) $0))))))))))))))))))) (%58 (\%395. (%32 (\%447. (%32
       (\%448. ((($3 $2) $1) $0))))))))))`)
  val lhsWithNullSfx_ind =
    DT(["DISK_THM"], [],
       `(%449 (\%450. ((%6 ((%18 (%58 (\%203. (($1 $0) %134)))) (%58
       (\%203. (%31 (\%73. (%32 (\%330. (%328 (\%329. ((%6 ((%18 ((%6 (%87
       ((%232 $3) $1))) (($4 $3) $0))) ((%6 ((%232 $3) $1)) (($4 $3) $0))))
       (($4 $3) ((%137 ((%15 $2) $1)) $0))))))))))))) (%58 (\%395. (%328
       (\%335. (($2 $1) $0))))))))`)
  val lhsWithNullSfx_def =
    DT(["DISK_THM"], [],
       `((%18 ((%125 ((%340 %203) %134)) %120)) ((%125 ((%340 %203) ((%137
       ((%15 %73) %330)) %329))) (((%122 ((%232 %203) %330)) ((%123 ((%149
       (%161 %73)) %144)) ((%340 %203) %329))) ((%340 %203) %329))))`)
  val sfxNotNull_ind =
    DT(["DISK_THM"], [],
       `(%451 (\%452. ((%6 ((%18 (%58 (\%203. (($1 $0) %453)))) (%58
       (\%203. (%347 (\%348. (%32 (\%330. (%349 (\%350. ((%6 ((%18 ((%6
       (%87 (%87 ((%232 $3) $1)))) (($4 $3) $0))) ((%6 (%87 ((%232 $3)
       $1))) (($4 $3) $0)))) (($4 $3) ((%352 ((%353 $2) $1))
       $0))))))))))))) (%58 (\%395. (%349 (\%357. (($2 $1) $0))))))))`)
  val sfxNotNull_def =
    DT(["DISK_THM"], [],
       `((%18 ((%125 ((%362 %203) %453)) %120)) ((%125 ((%362 %203) ((%352
       ((%353 %348) %330)) %350))) (((%122 (%87 ((%232 %203) %330))) ((%123
       %330) ((%362 %203) %350))) ((%362 %203) %350))))`)
  val notTmnlDerives =
    DT(["DISK_THM"], [],
       `(%32 (\%371. (%87 (((%208 %203) ((%149 (%257 %177)) %144)) $0))))`)
  val notTlDerives =
    DT(["DISK_THM"], [],
       `(%347 (\%348. (%87 (((%208 %203) ((%149 (%257 %177)) %399))
       %144))))`)
  val notTmnlRtcDerives1 =
    DT(["DISK_THM"], [],
       `(%31 (\%251. (%32 (\%371. ((%6 (((%217 (%208 %203)) ((%149 (%257
       $1)) %144)) $0)) ((%75 $0) ((%149 (%257 $1)) %144)))))))`)
  val notTmnlRtcDerives2 =
    DT(["DISK_THM"], [],
       `(%347 (\%454. (%32 (\%371. ((%6 ((%75 $0) ((%149 (%257 %251))
       %144))) (((%217 (%208 %203)) ((%149 (%257 %251)) %144)) $0))))))`)
  val notTmnlRtcDerives =
    DT(["DISK_THM"], [],
       `(%347 (\%454. (%32 (\%371. ((%25 (((%217 (%208 %203)) ((%149 (%257
       %251)) %144)) $0)) ((%75 $0) ((%149 (%257 %251)) %144)))))))`)
  val n0_1 =
    DT(["DISK_THM"], [],
       `(%32 (\%455. (%32 (\%456. ((%6 (((%208 %203) $1) $0)) ((%6 ((%113
       (%257 %251)) $1)) ((%113 (%257 %251)) $0)))))))`)
  val mem_r1 =
    DT(["DISK_THM"], [],
       `(%457 (\%430. ((%25 (%87 ((%431 $0) %432))) (%458 (\%459. ((%460
       $0) $1))))))`)
  val notTlRtcDerives_r1 =
    DT(["DISK_THM"], [],
       `(%32 (\%398. (%32 (\%411. ((%6 (((%217 (%208 %203)) $1) $0)) ((%6
       (%8 (\%251. ((%113 (%257 $0)) $2)))) (%87 ((%75 $0) %144))))))))`)
  val notTlRtcDerives =
    DT(["DISK_THM"], [],
       `(%347 (\%454. (%420 (\%461. (%87 (((%217 (%208 %203)) ((%149 (%257
       %251)) %399)) %144))))))`)
  val n4_1 =
    DT(["DISK_THM"], [],
       `(%32 (\%209. (%32 (\%210. ((%6 (((%321 %203) %267) ((%200 $1) $0)))
       ((%18 (((%321 %203) %267) $1)) (((%321 %203) %267) $0)))))))`)
  val n4_2 =
    DT(["DISK_THM"], [],
       `(%32 (\%209. (%32 (\%210. ((%6 ((%18 (((%321 %203) %267) $1))
       (((%321 %203) %267) $0))) (((%321 %203) %267) ((%200 $1) $0)))))))`)
  val n4 =
    DT(["DISK_THM"], [],
       `(%32 (\%209. (%32 (\%210. ((%25 (((%321 %203) %267) ((%200 $1)
       $0))) ((%18 (((%321 %203) %267) $1)) (((%321 %203) %267) $0)))))))`)
  val n5 =
    DT(["DISK_THM"], [],
       `((%25 (((%217 (%208 %203)) ((%149 (%257 %251)) %144)) %144))
       (((%321 %203) %267) ((%149 (%257 %251)) %144)))`)
  val nullableEq1 =
    DT(["DISK_THM", "MK_THM"], [],
       `(%58 (\%203. (%32 (\%267. (%32 (\%371. ((%6 (((%321 $2) $1) $0))
       ((%232 $2) $0))))))))`)
  val x_4 =
    DT(["DISK_THM"], [],
       `(%58 (\%203. (%32 (\%267. (%32 (\%371. ((%6 ((%75 $0) ((%149 (%161
       %309)) %144))) ((%6 (%10 (\%74. ((%18 (((%208 $3) $1) $0)) ((%18
       ((%113 (%161 %309)) $0)) (((%321 $3) $2) $0)))))) (((%321 $2) $1)
       $0)))))))))`)
  val nullableEq =
    DT(["DISK_THM", "MK_THM"], [],
       `(%58 (\%203. (%32 (\%371. ((%25 (((%321 $1) %144) $0)) ((%232 $1)
       $0))))))`)
  val n6 =
    DT(["DISK_THM"], [],
       `(%111 (\%462. (%32 (\%463. ((%25 (((%321 %203) %144) ((%149 $1)
       $0))) ((%18 (((%321 %203) %144) ((%149 $1) %144))) (((%321 %203)
       %144) $0)))))))`)
  val n3 =
    DT(["DISK_THM"], [],
       `(%32 (\%209. (%32 (\%210. ((%6 (((%321 %203) %144) $1)) ((%6
       (((%321 %203) %144) $0)) (((%321 %203) %144) ((%200 $1) $0))))))))`)
  val n7 =
    DT(["DISK_THM", "MK_THM"], [],
       `(%111 (\%462. ((%25 (((%321 %203) %144) ((%149 $0) %144))) (((%217
       (%208 %203)) ((%149 $0) %144)) %144))))`)
  val lderivesImpDerives =
    DT(["DISK_THM"], [],
       `(%32 (\%398. (%32 (\%411. ((%6 (((%217 (%214 %203)) $1) $0)) ((%6
       ((%175 %168) $0)) (((%217 (%208 %203)) $1) $0)))))))`)
  val rderivesImpDerives =
    DT(["DISK_THM"], [],
       `(%32 (\%398. (%32 (\%411. ((%6 (((%217 (%215 %203)) $1) $0)) ((%6
       ((%175 %168) $0)) (((%217 (%208 %203)) $1) $0)))))))`)
  val drd =
    DT(["DISK_THM"], [],
       `(%32 (\%464. (%32 (\%455. (%32 (\%456. ((%6 (((%208 %203) $2) $1))
       ((%6 (((%215 %203) $1) $0)) (%10 (\%465. ((%18 (((%215 %203) $3)
       $0)) (((%208 %203) $0) $1))))))))))))`)
  val nrc_drd =
    DT(["DISK_THM"], [],
       `(%466 (\%16. (%32 (\%464. (%32 (\%455. ((%6 ((((%467 (%208 %203))
       (%468 $2)) $1) $0)) ((%6 ((%175 %168) $0)) (%10 (\%465. ((%18
       (((%215 %203) $2) $0)) ((((%467 (%208 %203)) $3) $0)
       $1))))))))))))`)
  val nrc_drdeq =
    DT(["DISK_THM"], [],
       `(%466 (\%16. (%32 (\%464. (%32 (\%455. ((%6 ((((%467 (%208 %203))
       $2) $1) $0)) ((%6 ((%175 %168) $0)) ((((%467 (%215 %203)) $2) $1)
       $0)))))))))`)
  val derivesImpRderives =
    DT(["DISK_THM"], [],
       `(%32 (\%464. (%32 (\%455. ((%6 (((%217 (%208 %203)) $1) $0)) ((%6
       ((%175 %168) $0)) (((%217 (%215 %203)) $1) $0)))))))`)
  val drd_langeq =
    DT(["DISK_THM"], [], `(%58 (\%203. ((%218 (%223 $0)) (%225 $0))))`)
  end
  val _ = DB.bindl "grammarDef"
  [("rule_TY_DEF",rule_TY_DEF,DB.Def), ("rule_repfns",rule_repfns,DB.Def),
   ("grammarDef0_def",grammarDef0_def,DB.Def), ("rule",rule,DB.Def),
   ("rule_case_def",rule_case_def,DB.Def),
   ("rule_size_def",rule_size_def,DB.Def),
   ("grammar_TY_DEF",grammar_TY_DEF,DB.Def),
   ("grammar_repfns",grammar_repfns,DB.Def),
   ("grammarDef1_def",grammarDef1_def,DB.Def), ("G",G,DB.Def),
   ("grammar_case_def",grammar_case_def,DB.Def),
   ("grammar_size_def",grammar_size_def,DB.Def),
   ("ruleRhs_def",ruleRhs_def,DB.Def), ("ruleLhs_def",ruleLhs_def,DB.Def),
   ("getRules_tupled_primitive_def",getRules_tupled_primitive_def,DB.Def),
   ("getRules_curried_def",getRules_curried_def,DB.Def),
   ("rhsWithSym_tupled_primitive_def",
    rhsWithSym_tupled_primitive_def,
    DB.Def), ("rhsWithSym_curried_def",rhsWithSym_curried_def,DB.Def),
   ("rulesWithSymInRhs_tupled_primitive_def",
    rulesWithSymInRhs_tupled_primitive_def,
    DB.Def),
   ("rulesWithSymInRhs_curried_def",rulesWithSymInRhs_curried_def,DB.Def),
   ("lhsWithLastSym_tupled_primitive_def",
    lhsWithLastSym_tupled_primitive_def,
    DB.Def),
   ("lhsWithLastSym_curried_def",lhsWithLastSym_curried_def,DB.Def),
   ("rule_terminals_def",rule_terminals_def,DB.Def),
   ("rule_nonterminals_def",rule_nonterminals_def,DB.Def),
   ("is_word_def",is_word_def,DB.Def), ("rules_def",rules_def,DB.Def),
   ("startSym_def",startSym_def,DB.Def),
   ("terminals_def",terminals_def,DB.Def),
   ("nonTerminals_def",nonTerminals_def,DB.Def),
   ("nonTerminalsML_primitive_def",nonTerminalsML_primitive_def,DB.Def),
   ("terminalsML_primitive_def",terminalsML_primitive_def,DB.Def),
   ("allSyms_def",allSyms_def,DB.Def),
   ("allSymsML_def",allSymsML_def,DB.Def),
   ("derives_def",derives_def,DB.Def),
   ("lderives_def",lderives_def,DB.Def),
   ("rderives_def",rderives_def,DB.Def), ("gaw_def",gaw_def,DB.Def),
   ("sforms_def",sforms_def,DB.Def), ("language_def",language_def,DB.Def),
   ("llanguage_def",llanguage_def,DB.Def),
   ("rlanguage_def",rlanguage_def,DB.Def),
   ("is_null_def",is_null_def,DB.Def),
   ("numTmnls_def",numTmnls_def,DB.Def),
   ("nullable_def",nullable_def,DB.Def),
   ("nr_defn_tupled_AUX_def",nr_defn_tupled_AUX_def,DB.Def),
   ("nr_defn_tupled_primitive_def",nr_defn_tupled_primitive_def,DB.Def),
   ("nr_defn_curried_def",nr_defn_curried_def,DB.Def),
   ("getRhs_tupled_primitive_def",getRhs_tupled_primitive_def,DB.Def),
   ("getRhs_curried_def",getRhs_curried_def,DB.Def),
   ("derivesNull_def",derivesNull_def,DB.Def),
   ("numNonTmnls_primitive_def",numNonTmnls_primitive_def,DB.Def),
   ("nullableList_tupled_AUX_def",nullableList_tupled_AUX_def,DB.Def),
   ("nullableList_tupled_primitive_def",
    nullableList_tupled_primitive_def,
    DB.Def), ("nullableList_curried_def",nullableList_curried_def,DB.Def),
   ("lhsWithNullSfx_tupled_primitive_def",
    lhsWithNullSfx_tupled_primitive_def,
    DB.Def),
   ("lhsWithNullSfx_curried_def",lhsWithNullSfx_curried_def,DB.Def),
   ("sfxNotNull_tupled_primitive_def",
    sfxNotNull_tupled_primitive_def,
    DB.Def), ("sfxNotNull_curried_def",sfxNotNull_curried_def,DB.Def),
   ("datatype_rule",datatype_rule,DB.Thm), ("rule_11",rule_11,DB.Thm),
   ("rule_case_cong",rule_case_cong,DB.Thm),
   ("rule_nchotomy",rule_nchotomy,DB.Thm),
   ("rule_Axiom",rule_Axiom,DB.Thm),
   ("rule_induction",rule_induction,DB.Thm),
   ("datatype_grammar",datatype_grammar,DB.Thm),
   ("grammar_11",grammar_11,DB.Thm),
   ("grammar_case_cong",grammar_case_cong,DB.Thm),
   ("grammar_nchotomy",grammar_nchotomy,DB.Thm),
   ("grammar_Axiom",grammar_Axiom,DB.Thm),
   ("grammar_induction",grammar_induction,DB.Thm),
   ("getRules_ind",getRules_ind,DB.Thm),
   ("getRules_def",getRules_def,DB.Thm),
   ("rhsWithSym_ind",rhsWithSym_ind,DB.Thm),
   ("rhsWithSym_def",rhsWithSym_def,DB.Thm),
   ("rulesWithSymInRhs_ind",rulesWithSymInRhs_ind,DB.Thm),
   ("rulesWithSymInRhs_def",rulesWithSymInRhs_def,DB.Thm),
   ("lhsWithLastSym_ind",lhsWithLastSym_ind,DB.Thm),
   ("lhsWithLastSym_def",lhsWithLastSym_def,DB.Thm),
   ("lwls_r1",lwls_r1,DB.Thm),
   ("notNullLhsLastSym",notNullLhsLastSym,DB.Thm),
   ("nonTerminalsML_ind",nonTerminalsML_ind,DB.Thm),
   ("nonTerminalsML_def",nonTerminalsML_def,DB.Thm),
   ("terminalsML_ind",terminalsML_ind,DB.Thm),
   ("terminalsML_def",terminalsML_def,DB.Thm),
   ("nonTerminalsEq",nonTerminalsEq,DB.Thm),
   ("terminalsEq",terminalsEq,DB.Thm), ("allSymsEq",allSymsEq,DB.Thm),
   ("derives_same_append_left",derives_same_append_left,DB.Thm),
   ("derives_same_append_right",derives_same_append_right,DB.Thm),
   ("rtc_derives_same_append_left",rtc_derives_same_append_left,DB.Thm),
   ("b1",b1,DB.Thm),
   ("rtc_derives_same_append_right",rtc_derives_same_append_right,DB.Thm),
   ("derives_append",derives_append,DB.Thm), ("res1",res1,DB.Thm),
   ("res2",res2,DB.Thm), ("res3",res3,DB.Thm), ("slres",slres,DB.Thm),
   ("slres2",slres2,DB.Thm), ("rgr_r8",rgr_r8,DB.Thm),
   ("sub_result",sub_result,DB.Thm), ("key_result",key_result,DB.Thm),
   ("sub_result_rev",sub_result_rev,DB.Thm),
   ("term_syms_gen_words",term_syms_gen_words,DB.Thm),
   ("upgr_r7",upgr_r7,DB.Thm), ("lupgr_r7",lupgr_r7,DB.Thm),
   ("upgr_r11",upgr_r11,DB.Thm), ("lupgr_r11",lupgr_r11,DB.Thm),
   ("upgr_r15",upgr_r15,DB.Thm), ("rtc_r1",rtc_r1,DB.Thm),
   ("upgr_r18",upgr_r18,DB.Thm), ("lemma2",lemma2,DB.Thm),
   ("llemma2",llemma2,DB.Thm), ("upgr_r17",upgr_r17,DB.Thm),
   ("lupgr_r17",lupgr_r17,DB.Thm), ("upgr_r19",upgr_r19,DB.Thm),
   ("lupgr_r19",lupgr_r19,DB.Thm), ("slemma1_4",slemma1_4,DB.Thm),
   ("slemma1_3",slemma1_3,DB.Thm), ("emptySetList",emptySetList,DB.Thm),
   ("finiteNtsList",finiteNtsList,DB.Thm), ("rt1",rt1,DB.Thm),
   ("rt2",rt2,DB.Thm), ("rt",rt,DB.Thm),
   ("ntsNotInTmnls1",ntsNotInTmnls1,DB.Thm),
   ("ntsNotInTmnls",ntsNotInTmnls,DB.Thm), ("rnt1",rnt1,DB.Thm),
   ("rnt2",rnt2,DB.Thm), ("rnt",rnt,DB.Thm),
   ("tsNotInNonTmnls",tsNotInNonTmnls,DB.Thm),
   ("allNtSymsInGr",allNtSymsInGr,DB.Thm),
   ("allTmSymsInGr",allTmSymsInGr,DB.Thm), ("symInGr",symInGr,DB.Thm),
   ("finiteTerminals",finiteTerminals,DB.Thm),
   ("finiteAllSyms",finiteAllSyms,DB.Thm),
   ("getRhs_ind",getRhs_ind,DB.Thm), ("getRhs_def",getRhs_def,DB.Thm),
   ("numNonTmnls_ind",numNonTmnls_ind,DB.Thm),
   ("numNonTmnls_def",numNonTmnls_def,DB.Thm),
   ("getRhsDistrib",getRhsDistrib,DB.Thm), ("x_1",x_1,DB.Thm),
   ("notNullGetRhs_1",notNullGetRhs_1,DB.Thm),
   ("notNullGetRhs_2",notNullGetRhs_2,DB.Thm),
   ("notNullGetRhs",notNullGetRhs,DB.Thm), ("ntsInGr",ntsInGr,DB.Thm),
   ("nullableML",nullableML,DB.Thm),
   ("nullableML_ind",nullableML_ind,DB.Thm),
   ("lhsWithNullSfx_ind",lhsWithNullSfx_ind,DB.Thm),
   ("lhsWithNullSfx_def",lhsWithNullSfx_def,DB.Thm),
   ("sfxNotNull_ind",sfxNotNull_ind,DB.Thm),
   ("sfxNotNull_def",sfxNotNull_def,DB.Thm),
   ("notTmnlDerives",notTmnlDerives,DB.Thm),
   ("notTlDerives",notTlDerives,DB.Thm),
   ("notTmnlRtcDerives1",notTmnlRtcDerives1,DB.Thm),
   ("notTmnlRtcDerives2",notTmnlRtcDerives2,DB.Thm),
   ("notTmnlRtcDerives",notTmnlRtcDerives,DB.Thm), ("n0_1",n0_1,DB.Thm),
   ("mem_r1",mem_r1,DB.Thm),
   ("notTlRtcDerives_r1",notTlRtcDerives_r1,DB.Thm),
   ("notTlRtcDerives",notTlRtcDerives,DB.Thm), ("n4_1",n4_1,DB.Thm),
   ("n4_2",n4_2,DB.Thm), ("n4",n4,DB.Thm), ("n5",n5,DB.Thm),
   ("nullableEq1",nullableEq1,DB.Thm), ("x_4",x_4,DB.Thm),
   ("nullableEq",nullableEq,DB.Thm), ("n6",n6,DB.Thm), ("n3",n3,DB.Thm),
   ("n7",n7,DB.Thm), ("lderivesImpDerives",lderivesImpDerives,DB.Thm),
   ("rderivesImpDerives",rderivesImpDerives,DB.Thm), ("drd",drd,DB.Thm),
   ("nrc_drd",nrc_drd,DB.Thm), ("nrc_drdeq",nrc_drdeq,DB.Thm),
   ("derivesImpRderives",derivesImpRderives,DB.Thm),
   ("drd_langeq",drd_langeq,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("setLemmasTheory.setLemmas_grammars",
                          setLemmasTheory.setLemmas_grammars),
                         ("regexpTheory.regexp_grammars",
                          regexpTheory.regexp_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "set")
        {Name = "LIST_TO_SET", Thy = "list"}
  val _ = update_grms temp_add_type "rule"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_rule")
        {Name = "dest_rule", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_rule")
        {Name = "mk_rule", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "grammarDef0")
        {Name = "grammarDef0", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rule")
        {Name = "rule", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rule_case")
        {Name = "rule_case", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rule_size")
        {Name = "rule_size", Thy = "grammarDef"}
  val _ = update_grms temp_add_type "grammar"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_grammar")
        {Name = "dest_grammar", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_grammar")
        {Name = "mk_grammar", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "grammarDef1")
        {Name = "grammarDef1", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "G")
        {Name = "G", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "grammar_case")
        {Name = "grammar_case", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "grammar_size")
        {Name = "grammar_size", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ruleRhs")
        {Name = "ruleRhs", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ruleLhs")
        {Name = "ruleLhs", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getRules_tupled")
        {Name = "getRules_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getRules")
        {Name = "getRules", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rhsWithSym_tupled")
        {Name = "rhsWithSym_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rhsWithSym")
        {Name = "rhsWithSym", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rulesWithSymInRhs_tupled")
        {Name = "rulesWithSymInRhs_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rulesWithSymInRhs")
        {Name = "rulesWithSymInRhs", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lhsWithLastSym_tupled")
        {Name = "lhsWithLastSym_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lhsWithLastSym")
        {Name = "lhsWithLastSym", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rule_terminals")
        {Name = "rule_terminals", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rule_nonterminals")
        {Name = "rule_nonterminals", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "is_word")
        {Name = "is_word", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rules")
        {Name = "rules", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "startSym")
        {Name = "startSym", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "terminals")
        {Name = "terminals", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nonTerminals")
        {Name = "nonTerminals", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nonTerminalsML")
        {Name = "nonTerminalsML", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "terminalsML")
        {Name = "terminalsML", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "allSyms")
        {Name = "allSyms", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "allSymsML")
        {Name = "allSymsML", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "derives")
        {Name = "derives", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lderives")
        {Name = "lderives", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rderives")
        {Name = "rderives", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "gaw")
        {Name = "gaw", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sforms")
        {Name = "sforms", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "language")
        {Name = "language", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "llanguage")
        {Name = "llanguage", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rlanguage")
        {Name = "rlanguage", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "is_null")
        {Name = "is_null", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "numTmnls")
        {Name = "numTmnls", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nullable")
        {Name = "nullable", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nr_defn_tupled_aux")
        {Name = "nr_defn_tupled_aux", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nr_defn_tupled")
        {Name = "nr_defn_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nr")
        {Name = "nr", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getRhs_tupled")
        {Name = "getRhs_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getRhs")
        {Name = "getRhs", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "derivesNull")
        {Name = "derivesNull", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "numNonTmnls")
        {Name = "numNonTmnls", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nullableList_tupled_aux")
        {Name = "nullableList_tupled_aux", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nullableList_tupled")
        {Name = "nullableList_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nullableML")
        {Name = "nullableML", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lhsWithNullSfx_tupled")
        {Name = "lhsWithNullSfx_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "lhsWithNullSfx")
        {Name = "lhsWithNullSfx", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sfxNotNull_tupled")
        {Name = "sfxNotNull_tupled", Thy = "grammarDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sfxNotNull")
        {Name = "sfxNotNull", Thy = "grammarDef"}
  val grammarDef_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG rule_Axiom,
           case_def=rule_case_def,
           case_cong=rule_case_cong,
           induction=ORIG rule_induction,
           nchotomy=rule_nchotomy,
           size=SOME(Parse.Term`(grammarDef$rule_size) :(grammarDef$rule) -> (num$num)`,
                     ORIG rule_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME rule_11,
           distinct=NONE,
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
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG grammar_Axiom,
           case_def=grammar_case_def,
           case_cong=grammar_case_cong,
           induction=ORIG grammar_induction,
           nchotomy=grammar_nchotomy,
           size=SOME(Parse.Term`(grammarDef$grammar_size) :(grammarDef$grammar) -> (num$num)`,
                     ORIG grammar_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME grammar_11,
           distinct=NONE,
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
  
  
  val _ = computeLib.add_funs [ruleRhs_def];  
  
  val _ = computeLib.add_funs [ruleLhs_def];  
  
  val _ = computeLib.add_funs [getRules_def];  
  
  val _ = computeLib.add_funs [rhsWithSym_def];  
  
  val _ = computeLib.add_funs [rulesWithSymInRhs_def];  
  
  val _ = computeLib.add_funs [lhsWithLastSym_def];  
  
  val _ = computeLib.add_funs [rule_terminals_def];  
  
  val _ = computeLib.add_funs [rule_nonterminals_def];  
  
  val _ = computeLib.add_funs [is_word_def];  
  
  val _ = computeLib.add_funs [rules_def];  
  
  val _ = computeLib.add_funs [startSym_def];  
  
  val _ = computeLib.add_funs [terminals_def];  
  
  val _ = computeLib.add_funs [nonTerminals_def];  
  
  val _ = computeLib.add_funs [nonTerminalsML_def];  
  
  val _ = computeLib.add_funs [terminalsML_def];  
  
  val _ = computeLib.add_funs [allSyms_def];  
  
  val _ = computeLib.add_funs [allSymsML_def];  
  
  val _ = computeLib.add_funs [derives_def];  
  
  val _ = computeLib.add_funs [lderives_def];  
  
  val _ = computeLib.add_funs [rderives_def];  
  
  val _ = computeLib.add_funs [gaw_def];  
  
  val _ = computeLib.add_funs [sforms_def];  
  
  val _ = computeLib.add_funs [language_def];  
  
  val _ = computeLib.add_funs [llanguage_def];  
  
  val _ = computeLib.add_funs [rlanguage_def];  
  
  val _ = computeLib.add_funs [is_null_def];  
  
  val _ = computeLib.add_funs [numTmnls_def];  
  
  val _ = computeLib.add_funs [nullable_def];  
  
  val _ = computeLib.add_funs [getRhs_def];  
  
  val _ = computeLib.add_funs [derivesNull_def];  
  
  val _ = computeLib.add_funs [numNonTmnls_def];  
  
  val _ = computeLib.add_funs [lhsWithNullSfx_def];  
  
  val _ = computeLib.add_funs [sfxNotNull_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
