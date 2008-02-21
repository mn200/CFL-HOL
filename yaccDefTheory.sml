structure yaccDefTheory :> yaccDefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading yaccDefTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open followSetDefTheory
  in end;
  val _ = Theory.link_parents
          ("yaccDef",
          Arbnum.fromString "1203551220",
          Arbnum.fromString "599001")
          [("followSetDef",
           Arbnum.fromString "1203551207",
           Arbnum.fromString "541097")];
  val _ = Theory.incorporate_types "yaccDef" [];
  val _ = Theory.incorporate_consts "yaccDef"
     [("validItem",
       ((T"grammar" "grammarDef" [] -->
         (T"item" "parserDef" [] --> bool)))),
      ("asNeighbours",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"list" "list" [T"symbol" "regexp" []] -->
           T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))))),
      ("getState",
       ((T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] --> T"action" "parserDef" []))))),
      ("buildTree",
       ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]
         -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          T"option" "option"
           [T"list" "list" [T"ptree" "parseTree" []]])))),
      ("initProds2Items",
       ((T"string" "string" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list" [T"item" "parserDef" []])))),
      ("yacc",
       ((T"grammar" "grammarDef" [] -->
         (T"string" "string" [] -->
          (T"string" "string" [] -->
           (T"list" "list" [T"symbol" "regexp" []] -->
            T"option" "option" [T"ptree" "parseTree" []])))))),
      ("iclosure",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          T"list" "list" [T"item" "parserDef" []])))),
      ("itemLhs",((T"item" "parserDef" [] --> T"string" "string" []))),
      ("validItem_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [], T"item" "parserDef" []] --> bool))),
      ("doReduce_tupled",
       ((T"prod" "pair"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])), alpha],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"prod" "pair"
                [T"list" "list"
                  [T"prod" "pair"
                    [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                 T"list" "list" [T"state" "parserDef" []]]],
             T"rule" "grammarDef" []]] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]))),
      ("validItl_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] --> bool))),
      ("itemFstRhs",
       ((T"item" "parserDef" [] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("nextState",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []]))))),
      ("allItems",
       ((T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"item" "parserDef" []]))),
      ("slrML4Sym",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
          (T"symbol" "regexp" [] -->
           T"option" "option"
            [T"prod" "pair"
              [(T"list" "list" [T"item" "parserDef" []] -->
                (T"symbol" "regexp" [] -->
                 T"list" "list" [T"item" "parserDef" []])),
               (T"list" "list" [T"item" "parserDef" []] -->
                (T"string" "string" [] -->
                 T"list" "list" [T"rule" "grammarDef" []]))]]))))),
      ("rules2Items",
       ((T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"item" "parserDef" []]))),
      ("validItl",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] --> bool)))),
      ("isGrammarItl",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] --> bool)))),
      ("reduce",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))))),
      ("getItems",
       ((T"list" "list" [T"rule" "grammarDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"item" "parserDef" []])))),
      ("visit",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
          (T"list" "list" [T"item" "parserDef" []] -->
           T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))))),
      ("initItems",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] -->
          T"list" "list" [T"item" "parserDef" []])))),
      ("parse",
       ((T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]] -->
         (T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]] -->
          T"option" "option"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]]])))),
      ("parser",
       ((T"grammar" "grammarDef" [] -->
         (T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]] -->
          (T"list" "list" [T"symbol" "regexp" []] -->
           (T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
            (T"list" "list" [T"state" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              (T"symbol" "regexp" [] -->
               T"option" "option"
                [T"option" "option" [T"ptree" "parseTree" []]]))))))))),
      ("addRule",
       ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]
         -->
         (T"rule" "grammarDef" [] -->
          T"option" "option" [T"ptree" "parseTree" []])))),
      ("findItemInRules_tupled",
       ((T"prod" "pair"
          [T"item" "parserDef" [],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool))),
      ("visit_defn_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
             T"list" "list" [T"item" "parserDef" []]]] -->
         T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
      ("validStates_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"state" "parserDef" []]] --> bool))),
      ("itemPair",
       ((T"item" "parserDef" [] -->
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]))),
      ("ruleItems",
       ((T"item" "parserDef" [] -->
         T"list" "list" [T"item" "parserDef" []]))),
      ("iclosure1",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          T"list" "list" [T"item" "parserDef" []])))),
      ("iclosure_defn_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] -->
         T"list" "list" [T"item" "parserDef" []]))),
      ("doReduce",
       ((T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha] -->
         (T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]] -->
          (T"rule" "grammarDef" [] -->
           T"option" "option"
            [T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"prod" "pair"
                [T"list" "list"
                  [T"prod" "pair"
                    [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                 T"list" "list" [T"state" "parserDef" []]]]]))))),
      ("moveDot",
       ((T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])))),
      ("reduce_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"item" "parserDef" []],
             T"string" "string" []]] -->
         T"list" "list" [T"rule" "grammarDef" []]))),
      ("parse_tupled",
       ((T"prod" "pair"
          [T"option" "option"
            [T"prod" "pair"
              [(T"list" "list" [T"item" "parserDef" []] -->
                (T"symbol" "regexp" [] -->
                 T"list" "list" [T"item" "parserDef" []])),
               (T"list" "list" [T"item" "parserDef" []] -->
                (T"string" "string" [] -->
                 T"list" "list" [T"rule" "grammarDef" []]))]],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]))),
      ("iclosure1_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] -->
         T"list" "list" [T"item" "parserDef" []]))),
      ("initProds2Items_tupled",
       ((T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"item" "parserDef" []]))),
      ("itemSndRhs",
       ((T"item" "parserDef" [] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("slrML",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
          (T"list" "list" [T"symbol" "regexp" []] -->
           T"option" "option"
            [T"prod" "pair"
              [(T"list" "list" [T"item" "parserDef" []] -->
                (T"symbol" "regexp" [] -->
                 T"list" "list" [T"item" "parserDef" []])),
               (T"list" "list" [T"item" "parserDef" []] -->
                (T"string" "string" [] -->
                 T"list" "list" [T"rule" "grammarDef" []]))]]))))),
      ("itemEqRuleList_defn_tupled",
       ((T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool))),
      ("auggr",
       ((T"grammar" "grammarDef" [] -->
         (T"string" "string" [] -->
          (T"string" "string" [] -->
           T"option" "option" [T"grammar" "grammarDef" []]))))),
      ("findItemInRules",
       ((T"item" "parserDef" [] -->
         (T"list" "list" [T"rule" "grammarDef" []] --> bool)))),
      ("moveDot_tupled",
       ((T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
         --> T"list" "list" [T"item" "parserDef" []]))),
      ("symNeighbour",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []]))))),
      ("itemEqRuleList",
       ((T"list" "list" [T"item" "parserDef" []] -->
         (T"list" "list" [T"rule" "grammarDef" []] --> bool)))),
      ("sgoto",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []]))))),
      ("slr",
       ((T"grammar" "grammarDef" [] -->
         T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]]))),
      ("getItems_tupled",
       ((T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
         --> T"list" "list" [T"item" "parserDef" []]))),
      ("machine",
       ((T"grammar" "grammarDef" [] -->
         T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]))),
      ("validStates",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"state" "parserDef" []] --> bool)))),
      ("allGrammarItls",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"item" "parserDef" []] --> bool))))];
  
  local
  val share_table = Vector.fromList
  [C"=" "min"
    (((T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       --> T"list" "list" [T"item" "parserDef" []]) -->
      ((T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
        --> T"list" "list" [T"item" "parserDef" []]) --> bool))),
   C"getItems_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
      --> T"list" "list" [T"item" "parserDef" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
        --> bool)) -->
      (((T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
         --> T"list" "list" [T"item" "parserDef" []]) -->
        (T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
         --> T"list" "list" [T"item" "parserDef" []])) -->
       (T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
        --> T"list" "list" [T"item" "parserDef" []])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
        -->
        (T"prod" "pair"
          [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
      -->
      (T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       --> bool))), C"/\\" "bool" ((bool --> (bool --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
        --> bool)) --> bool)),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"r" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] --> bool) --> bool)),
   V"rs" (T"list" "list" [T"rule" "grammarDef" []]),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"s" (T"string" "string" []), V"l" (T"string" "string" []),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)),
   C"=" "min"
    ((T"string" "string" [] --> (T"string" "string" [] --> bool))),
   C"," "pair"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] -->
       T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []],
         T"string" "string" []]))),
   C"CONS" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   V"getItems_tupled"
    ((T"prod" "pair"
       [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
      --> T"list" "list" [T"item" "parserDef" []])),
   V"a"
    (T"prod" "pair"
      [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]),
   C"pair_case" "pair"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"string" "string" [] --> T"list" "list" [T"item" "parserDef" []]))
      -->
      (T"prod" "pair"
        [T"list" "list" [T"rule" "grammarDef" []], T"string" "string" []]
       --> T"list" "list" [T"item" "parserDef" []]))),
   V"v" (T"list" "list" [T"rule" "grammarDef" []]),
   C"list_case" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"I" "combin"
    ((T"list" "list" [T"item" "parserDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"NIL" "list" (T"list" "list" [T"item" "parserDef" []]),
   V"v2" (T"rule" "grammarDef" []),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"item" "parserDef" []])) -->
      (T"rule" "grammarDef" [] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"CONS" "list"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"item" "parserDef"
    ((T"string" "string" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"item" "parserDef" []))),
   C"," "pair"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]]))),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   V"x" (T"list" "list" [T"rule" "grammarDef" []]),
   V"x1" (T"string" "string" []),
   C"=" "min"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"getItems" "yaccDef"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"item" "parserDef" []]) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] -->
        T"list" "list" [T"item" "parserDef" []]) --> bool))),
   C"iclosure1_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] -->
         T"list" "list" [T"item" "parserDef" []]) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] --> bool)) --> bool)),
   V"l1" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   V"il" (T"list" "list" [T"item" "parserDef" []]),
   C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"g" (T"grammar" "grammarDef" []),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]]))),
   V"l2" (T"list" "list" [T"symbol" "regexp" []]),
   V"ts" (T"string" "string" []),
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   V"nt" (T"string" "string" []),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   V"iclosure1_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"a"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"list" "list" [T"item" "parserDef" []]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"item" "parserDef" []])) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"v1" (T"list" "list" [T"item" "parserDef" []]),
   C"list_case" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      ((T"item" "parserDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"item" "parserDef" []])))),
   V"v2" (T"item" "parserDef" []),
   C"item_case" "parserDef"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] -->
        T"list" "list" [T"item" "parserDef" []])) -->
      (T"item" "parserDef" [] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"v5"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"item" "parserDef" []])) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"v7" (T"list" "list" [T"symbol" "regexp" []]),
   C"list_case" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"item" "parserDef" []])))),
   V"v8" (T"symbol" "regexp" []),
   C"symbol_case" "regexp"
    (((T"string" "string" [] --> T"list" "list" [T"item" "parserDef" []])
      -->
      ((T"string" "string" [] --> T"list" "list" [T"item" "parserDef" []])
       -->
       (T"symbol" "regexp" [] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"APPEND" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"rules" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   V"x" (T"grammar" "grammarDef" []),
   V"x1" (T"list" "list" [T"item" "parserDef" []]),
   C"iclosure1" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"iclosure_defn_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"v3" (T"list" "list" [T"item" "parserDef" []]),
   C"!" "bool" (((T"item" "parserDef" [] --> bool) --> bool)),
   V"ril" (T"list" "list" [T"item" "parserDef" []]),
   V"al" (T"list" "list" [T"item" "parserDef" []]),
   C"rmDupes" "listLemmas"
    ((T"list" "list" [T"item" "parserDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"=" "min"
    (((T"item" "parserDef" [] --> bool) -->
      ((T"item" "parserDef" [] --> bool) --> bool))),
   C"LIST_TO_SET" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"item" "parserDef" [] --> bool))),
   V"iclosure_defn_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"v4" (T"item" "parserDef" []),
   V"v5" (T"list" "list" [T"item" "parserDef" []]),
   C"LET" "bool"
    (((T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]) -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"iclosure" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"=" "min"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"item" "parserDef" []]) -->
      ((T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"item" "parserDef" []]) --> bool))),
   C"rules2Items" "yaccDef"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"WFREC" "relation"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)) -->
      (((T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"item" "parserDef" []]) -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"item" "parserDef" []])))),
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
   V"rst" (T"list" "list" [T"rule" "grammarDef" []]),
   V"rules2Items"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"a" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v" (T"rule" "grammarDef" []), V"eof" (T"string" "string" []),
   C"=" "min"
    ((T"option" "option" [T"grammar" "grammarDef" []] -->
      (T"option" "option" [T"grammar" "grammarDef" []] --> bool))),
   C"auggr" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"string" "string" [] -->
       (T"string" "string" [] -->
        T"option" "option" [T"grammar" "grammarDef" []])))),
   C"COND" "bool"
    ((bool -->
      (T"option" "option" [T"grammar" "grammarDef" []] -->
       (T"option" "option" [T"grammar" "grammarDef" []] -->
        T"option" "option" [T"grammar" "grammarDef" []])))),
   C"IN" "bool"
    ((T"symbol" "regexp" [] -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   C"nonTerminalsML" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"SOME" "option"
    ((T"grammar" "grammarDef" [] -->
      T"option" "option" [T"grammar" "grammarDef" []])),
   C"G" "grammarDef"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] --> T"grammar" "grammarDef" []))),
   C"APPEND" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"startSym" "grammarDef"
    ((T"grammar" "grammarDef" [] --> T"string" "string" [])),
   C"NIL" "list" (T"list" "list" [T"rule" "grammarDef" []]),
   C"NONE" "option" (T"option" "option" [T"grammar" "grammarDef" []]),
   C"=" "min"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"item" "parserDef" []]) -->
      ((T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"item" "parserDef" []]) --> bool))),
   C"initProds2Items_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"item" "parserDef" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"item" "parserDef" []]) -->
        (T"prod" "pair"
          [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
         --> T"list" "list" [T"item" "parserDef" []])) -->
       (T"prod" "pair"
         [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> T"list" "list" [T"item" "parserDef" []])))),
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
   C"," "pair"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"string" "string" [],
         T"list" "list" [T"rule" "grammarDef" []]]))),
   V"initProds2Items_tupled"
    ((T"prod" "pair"
       [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> T"list" "list" [T"item" "parserDef" []])),
   V"a"
    (T"prod" "pair"
      [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]),
   C"pair_case" "pair"
    (((T"string" "string" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"item" "parserDef" []])) -->
      (T"prod" "pair"
        [T"string" "string" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> T"list" "list" [T"item" "parserDef" []]))),
   V"v1" (T"list" "list" [T"rule" "grammarDef" []]),
   V"x" (T"string" "string" []),
   V"x1" (T"list" "list" [T"rule" "grammarDef" []]),
   C"initProds2Items" "yaccDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"r" (T"list" "list" [T"rule" "grammarDef" []]),
   C"initItems" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
       --> T"list" "list" [T"item" "parserDef" []]) -->
      ((T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
        --> T"list" "list" [T"item" "parserDef" []]) --> bool))),
   C"moveDot_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
        --> bool)) -->
      (((T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
         --> T"list" "list" [T"item" "parserDef" []]) -->
        (T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
         --> T"list" "list" [T"item" "parserDef" []])) -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
        --> T"list" "list" [T"item" "parserDef" []])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
        -->
        (T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
         --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []] -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
       -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
        --> bool)) --> bool)),
   V"ss" (T"list" "list" [T"symbol" "regexp" []]),
   V"a" (T"list" "list" [T"symbol" "regexp" []]),
   V"str" (T"string" "string" []),
   V"it" (T"list" "list" [T"item" "parserDef" []]),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"sym" (T"symbol" "regexp" []), V"s" (T"symbol" "regexp" []),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"," "pair"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"symbol" "regexp" [] -->
       T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"symbol" "regexp" []]))),
   V"v8" (T"list" "list" [T"symbol" "regexp" []]),
   V"v4" (T"string" "string" []),
   V"moveDot_tupled"
    ((T"prod" "pair"
       [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"a'"
    (T"prod" "pair"
      [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]),
   C"pair_case" "pair"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] --> T"list" "list" [T"item" "parserDef" []]))
      -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"symbol" "regexp" []]
       --> T"list" "list" [T"item" "parserDef" []]))),
   V"v" (T"list" "list" [T"item" "parserDef" []]),
   V"v7"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   V"v11" (T"list" "list" [T"symbol" "regexp" []]),
   C"APPEND" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"x" (T"list" "list" [T"item" "parserDef" []]),
   V"x1" (T"symbol" "regexp" []),
   C"moveDot" "yaccDef"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"symbol" "regexp" [] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"itl" (T"list" "list" [T"item" "parserDef" []]),
   C"nextState" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] --> bool) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] --> bool) --> bool))),
   C"validItl_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] --> bool) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"item" "parserDef" []]] --> bool)) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"item" "parserDef" []]] --> bool)))),
   V"rst" (T"list" "list" [T"item" "parserDef" []]),
   V"r2" (T"list" "list" [T"symbol" "regexp" []]),
   V"r1" (T"list" "list" [T"symbol" "regexp" []]),
   C"MEM" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   V"validItl_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"item" "parserDef" []]] --> bool)),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"list" "list" [T"item" "parserDef" []] --> bool)) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"item" "parserDef" []]] --> bool))),
   C"list_case" "list"
    ((bool -->
      ((T"item" "parserDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] --> bool)) -->
       (T"list" "list" [T"item" "parserDef" []] --> bool)))),
   C"I" "combin" ((bool --> bool)), C"T" "bool" (bool),
   C"item_case" "parserDef"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] --> bool)) -->
      (T"item" "parserDef" [] --> bool))),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   C"=" "min" ((bool --> (bool --> bool))),
   C"validItl" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]] --> bool) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"state" "parserDef" []]] --> bool) --> bool))),
   C"validStates_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"state" "parserDef" []]] --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"state" "parserDef" []]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"state" "parserDef" []]] --> bool) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"state" "parserDef" []]] --> bool)) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"state" "parserDef" []]] --> bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"state" "parserDef" []]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"list" "list" [T"state" "parserDef" []]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"state" "parserDef" []]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"state" "parserDef" []]] -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"list" "list" [T"state" "parserDef" []]] --> bool)) --> bool)),
   C"!" "bool"
    (((T"list" "list" [T"state" "parserDef" []] --> bool) --> bool)),
   V"rst" (T"list" "list" [T"state" "parserDef" []]),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"state" "parserDef" []] -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]]))),
   C"CONS" "list"
    ((T"state" "parserDef" [] -->
      (T"list" "list" [T"state" "parserDef" []] -->
       T"list" "list" [T"state" "parserDef" []]))),
   C"state" "parserDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"state" "parserDef" []))),
   V"validStates_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"list" "list" [T"state" "parserDef" []]] --> bool)),
   V"a"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"list" "list" [T"state" "parserDef" []]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"list" "list" [T"state" "parserDef" []] --> bool)) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"list" "list" [T"state" "parserDef" []]] --> bool))),
   V"v1" (T"list" "list" [T"state" "parserDef" []]),
   C"list_case" "list"
    ((bool -->
      ((T"state" "parserDef" [] -->
        (T"list" "list" [T"state" "parserDef" []] --> bool)) -->
       (T"list" "list" [T"state" "parserDef" []] --> bool)))),
   V"v2" (T"state" "parserDef" []),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] --> bool)) -->
      (T"state" "parserDef" [] --> bool))),
   V"x1" (T"list" "list" [T"state" "parserDef" []]),
   C"validStates" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"state" "parserDef" []] --> bool))),
   C"sgoto" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
       --> T"list" "list" [T"rule" "grammarDef" []]) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"item" "parserDef" []],
            T"string" "string" []]] -->
        T"list" "list" [T"rule" "grammarDef" []]) --> bool))),
   C"reduce_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
      --> T"list" "list" [T"rule" "grammarDef" []])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"item" "parserDef" []],
            T"string" "string" []]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"item" "parserDef" []],
             T"string" "string" []]] -->
         T"list" "list" [T"rule" "grammarDef" []]) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"item" "parserDef" []],
             T"string" "string" []]] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"item" "parserDef" []],
            T"string" "string" []]] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"item" "parserDef" []],
            T"string" "string" []]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"item" "parserDef" []],
             T"string" "string" []]] --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"item" "parserDef" []],
            T"string" "string" []]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"item" "parserDef" []],
            T"string" "string" []]] --> bool)) --> bool)),
   C"followSetML" "followSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool)))),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]
       -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []],
           T"string" "string" []]]))),
   C"," "pair"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"string" "string" [] -->
       T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"string" "string" []]))), V"v10" (T"symbol" "regexp" []),
   V"reduce_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
      --> T"list" "list" [T"rule" "grammarDef" []])),
   V"a"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]
        --> T"list" "list" [T"rule" "grammarDef" []])) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]]
       --> T"list" "list" [T"rule" "grammarDef" []]))),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]),
   C"pair_case" "pair"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"string" "string" [] -->
        T"list" "list" [T"rule" "grammarDef" []])) -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []], T"string" "string" []]
       --> T"list" "list" [T"rule" "grammarDef" []]))),
   V"v2" (T"list" "list" [T"item" "parserDef" []]),
   C"list_case" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      ((T"item" "parserDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   C"I" "combin"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"item_case" "parserDef"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] -->
        T"list" "list" [T"rule" "grammarDef" []])) -->
      (T"item" "parserDef" [] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"rule" "grammarDef" []])) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   V"v9" (T"list" "list" [T"symbol" "regexp" []]),
   C"list_case" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   V"v12" (T"symbol" "regexp" []),
   V"v13" (T"list" "list" [T"symbol" "regexp" []]),
   V"x2" (T"string" "string" []),
   C"=" "min"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"reduce" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"string" "string" [] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       bool) --> bool)),
   V"p" (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
      (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
       bool))),
   C"buildTree" "yaccDef"
    ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]))),
   C"LET" "bool"
    (((T"option" "option" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]) -->
      (T"option" "option" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]))),
   V"s" (T"option" "option" [T"list" "list" [T"symbol" "regexp" []]]),
   C"COND" "bool"
    ((bool -->
      (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
       (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
        T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]])))),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [T"symbol" "regexp" []]] -->
      (T"option" "option" [T"list" "list" [T"symbol" "regexp" []]] -->
       bool))),
   C"NONE" "option"
    (T"option" "option" [T"list" "list" [T"symbol" "regexp" []]]),
   C"NONE" "option"
    (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]))),
   C"LENGTH" "list"
    ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" [])),
   C"MAP" "list"
    (((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []) -->
      (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"SND" "pair"
    ((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
      T"ptree" "parseTree" [])),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"MAP" "list"
    (((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
       T"symbol" "regexp" []) -->
      (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"o" "combin"
    (((T"ptree" "parseTree" [] --> T"symbol" "regexp" []) -->
      ((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
        T"ptree" "parseTree" []) -->
       (T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
        T"symbol" "regexp" [])))),
   C"ptree2Sym" "parseTree"
    ((T"ptree" "parseTree" [] --> T"symbol" "regexp" [])),
   C"=" "min"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      (T"option" "option" [T"ptree" "parseTree" []] --> bool))),
   C"addRule" "yaccDef"
    ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
      (T"rule" "grammarDef" [] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   C"LET" "bool"
    (((T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
       T"option" "option" [T"ptree" "parseTree" []]) -->
      (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   V"x" (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]),
   C"COND" "bool"
    ((bool -->
      (T"option" "option" [T"ptree" "parseTree" []] -->
       (T"option" "option" [T"ptree" "parseTree" []] -->
        T"option" "option" [T"ptree" "parseTree" []])))),
   C"NONE" "option" (T"option" "option" [T"ptree" "parseTree" []]),
   C"SOME" "option"
    ((T"ptree" "parseTree" [] -->
      T"option" "option" [T"ptree" "parseTree" []])),
   C"Node" "parseTree"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []))),
   C"NT" "parseTree"
    ((T"string" "string" [] --> T"nonTerminal" "parseTree" [])),
   C"REVERSE" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"ptree" "parseTree" []])),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
      T"list" "list" [T"ptree" "parseTree" []])),
   C"REVERSE" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"=" "min"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])),
        (T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []]))] -->
      (T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))] --> bool))),
   C"machine" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])),
        (T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []]))])),
   C"," "pair"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] --> T"list" "list" [T"item" "parserDef" []]))
      -->
      ((T"list" "list" [T"item" "parserDef" []] -->
        (T"string" "string" [] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]))),
   C"=" "min"
    ((T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]] -->
      (T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] --> bool))),
   C"slr" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]])),
   C"LET" "bool"
    ((((T"list" "list" [T"item" "parserDef" []] -->
        (T"string" "string" [] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]) -->
      ((T"list" "list" [T"item" "parserDef" []] -->
        (T"string" "string" [] -->
         T"list" "list" [T"rule" "grammarDef" []])) -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]))),
   C"LET" "bool"
    ((((T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       ((T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []])) -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])) -->
      ((T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       ((T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []])) -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])))),
   V"sg"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"symbol" "regexp" [] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"red"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"string" "string" [] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"COND" "bool"
    ((bool -->
      (T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] -->
       (T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]] -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])))),
   C"?" "bool"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   C"?" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   C"LET" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] --> bool) -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"LET" "bool"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)) -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)))),
   V"s" (T"list" "list" [T"item" "parserDef" []]),
   C"pair_case" "pair"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)) -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] --> bool))),
   V"v3" (T"list" "list" [T"rule" "grammarDef" []]),
   C"list_case" "list"
    ((bool -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> bool)) -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)))),
   C"F" "bool" (bool), V"v12" (T"rule" "grammarDef" []),
   V"v13" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v16" (T"rule" "grammarDef" []),
   V"v17" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v8" (T"item" "parserDef" []),
   V"v9" (T"list" "list" [T"item" "parserDef" []]),
   V"v20" (T"rule" "grammarDef" []),
   V"v21" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v26" (T"rule" "grammarDef" []),
   V"v27" (T"list" "list" [T"rule" "grammarDef" []]),
   C"," "pair"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]]))),
   C"sym2Str" "regexp" ((T"symbol" "regexp" [] --> T"string" "string" [])),
   C"NONE" "option"
    (T"option" "option"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]]),
   C"SOME" "option"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])),
        (T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []]))] -->
      T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]])),
   C"=" "min"
    (((T"item" "parserDef" [] --> T"list" "list" [T"item" "parserDef" []])
      -->
      ((T"item" "parserDef" [] --> T"list" "list" [T"item" "parserDef" []])
       --> bool))),
   C"ruleItems" "yaccDef"
    ((T"item" "parserDef" [] --> T"list" "list" [T"item" "parserDef" []])),
   C"WFREC" "relation"
    (((T"item" "parserDef" [] --> (T"item" "parserDef" [] --> bool)) -->
      (((T"item" "parserDef" [] -->
         T"list" "list" [T"item" "parserDef" []]) -->
        (T"item" "parserDef" [] -->
         T"list" "list" [T"item" "parserDef" []])) -->
       (T"item" "parserDef" [] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"@" "min"
    ((((T"item" "parserDef" [] --> (T"item" "parserDef" [] --> bool)) -->
       bool) -->
      (T"item" "parserDef" [] --> (T"item" "parserDef" [] --> bool)))),
   V"R" ((T"item" "parserDef" [] --> (T"item" "parserDef" [] --> bool))),
   C"WF" "relation"
    (((T"item" "parserDef" [] --> (T"item" "parserDef" [] --> bool)) -->
      bool)), V"xs" (T"list" "list" [T"symbol" "regexp" []]),
   V"x" (T"symbol" "regexp" []), V"v6" (T"symbol" "regexp" []),
   V"ruleItems"
    ((T"item" "parserDef" [] --> T"list" "list" [T"item" "parserDef" []])),
   V"a" (T"item" "parserDef" []),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   V"v2" (T"list" "list" [T"symbol" "regexp" []]),
   V"v3" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool"
    (((T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool) --> bool)),
   V"x"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"=" "min"
    ((T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"list" "list" [T"symbol" "regexp" []]] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   C"itemPair" "yaccDef"
    ((T"item" "parserDef" [] -->
      T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"list" "list" [T"symbol" "regexp" []]])),
   C"allItems" "yaccDef"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"allItems"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"symNeighbour" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"=" "min"
    ((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       bool))),
   C"asNeighbours" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]])))),
   C"NIL" "list"
    (T"list" "list" [T"list" "list" [T"item" "parserDef" []]]),
   C"CONS" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
            T"list" "list" [T"item" "parserDef" []]]] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]]) -->
       bool))),
   C"visit_defn_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
          T"list" "list" [T"item" "parserDef" []]]] -->
      T"list" "list" [T"list" "list" [T"item" "parserDef" []]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
            T"list" "list" [T"item" "parserDef" []]]] --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
             T"list" "list" [T"item" "parserDef" []]]] -->
         T"list" "list" [T"list" "list" [T"item" "parserDef" []]]) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
             T"list" "list" [T"item" "parserDef" []]]] -->
         T"list" "list" [T"list" "list" [T"item" "parserDef" []]])) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
            T"list" "list" [T"item" "parserDef" []]]] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
            T"list" "list" [T"item" "parserDef" []]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
             T"list" "list" [T"item" "parserDef" []]]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
            T"list" "list" [T"item" "parserDef" []]]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
          T"list" "list" [T"item" "parserDef" []]]] -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
            T"list" "list" [T"item" "parserDef" []]]] --> bool)) -->
      bool)),
   C"!" "bool"
    (((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] --> bool)
      --> bool)),
   V"sn" (T"list" "list" [T"list" "list" [T"item" "parserDef" []]]),
   V"s" (T"list" "list" [T"list" "list" [T"item" "parserDef" []]]),
   V"rem" (T"list" "list" [T"list" "list" [T"item" "parserDef" []]]),
   V"a" (T"list" "list" [T"item" "parserDef" []]),
   C"\\/" "bool" ((bool --> (bool --> bool))),
   C"ALL_DISTINCT" "list"
    ((T"list" "list" [T"item" "parserDef" []] --> bool)),
   C"SET_TO_LIST" "container"
    (((T"symbol" "regexp" [] --> bool) -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"allSyms" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"diff" "listLemmas"
    ((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
   C"MEM" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       bool))),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
         T"list" "list" [T"item" "parserDef" []]] -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]]))),
   C"," "pair"
    ((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"prod" "pair"
        [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
         T"list" "list" [T"item" "parserDef" []]]))),
   C"APPEND" "list"
    ((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
   V"visit_defn_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
          T"list" "list" [T"item" "parserDef" []]]] -->
      T"list" "list" [T"list" "list" [T"item" "parserDef" []]])),
   V"a'"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"prod" "pair"
        [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
         T"list" "list" [T"item" "parserDef" []]]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
          T"list" "list" [T"item" "parserDef" []]] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]])) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
           T"list" "list" [T"item" "parserDef" []]]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
       T"list" "list" [T"item" "parserDef" []]]),
   C"pair_case" "pair"
    (((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]])) -->
      (T"prod" "pair"
        [T"list" "list" [T"list" "list" [T"item" "parserDef" []]],
         T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
   C"I" "combin"
    ((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
      T"list" "list" [T"list" "list" [T"item" "parserDef" []]])),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]])))),
   C"LET" "bool"
    (((T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]) -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]))),
   C"FLAT" "list"
    ((T"list" "list"
       [T"list" "list" [T"list" "list" [T"item" "parserDef" []]]] -->
      T"list" "list" [T"list" "list" [T"item" "parserDef" []]])),
   C"MAP" "list"
    (((T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"list" "list" [T"item" "parserDef" []]]) -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       T"list" "list"
        [T"list" "list" [T"list" "list" [T"item" "parserDef" []]]]))),
   V"x1" (T"list" "list" [T"list" "list" [T"item" "parserDef" []]]),
   V"x2" (T"list" "list" [T"item" "parserDef" []]),
   C"visit" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"list" "list" [T"item" "parserDef" []]])))),
   C"=" "min"
    (((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
       --> bool) -->
      ((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
        --> bool) --> bool))),
   C"validItem_tupled" "yaccDef"
    ((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
      --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
       -->
       (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
        --> bool)) -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [], T"item" "parserDef" []] --> bool)
        -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [], T"item" "parserDef" []] --> bool))
       -->
       (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
        --> bool)))),
   C"@" "min"
    ((((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
        -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [], T"item" "parserDef" []] --> bool))
       --> bool) -->
      (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
       -->
       (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
        --> bool)))),
   V"R"
    ((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
      -->
      (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
       -->
       (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
        --> bool)) --> bool)),
   V"validItem_tupled"
    ((T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
      --> bool)),
   V"a"
    (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] --> (T"item" "parserDef" [] --> bool))
      -->
      (T"prod" "pair" [T"grammar" "grammarDef" [], T"item" "parserDef" []]
       --> bool))), V"v1" (T"item" "parserDef" []),
   V"v3"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   V"x1" (T"item" "parserDef" []),
   C"validItem" "yaccDef"
    ((T"grammar" "grammarDef" [] --> (T"item" "parserDef" [] --> bool))),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"item" "parserDef" [] -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [], T"item" "parserDef" []]))),
   C"isGrammarItl" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"EVERY" "list"
    (((T"item" "parserDef" [] --> bool) -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"=" "min"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) -->
      ((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool))),
   C"allGrammarItls" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"GSPEC" "pred_set"
    (((T"list" "list" [T"item" "parserDef" []] -->
       T"prod" "pair" [T"list" "list" [T"item" "parserDef" []], bool]) -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"," "pair"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (bool -->
       T"prod" "pair" [T"list" "list" [T"item" "parserDef" []], bool]))),
   V"r"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"itemLhs" "yaccDef"
    ((T"item" "parserDef" [] --> T"string" "string" [])),
   C"itemFstRhs" "yaccDef"
    ((T"item" "parserDef" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"FST" "pair"
    ((T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"itemSndRhs" "yaccDef"
    ((T"item" "parserDef" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"SND" "pair"
    ((T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"slrML4Sym" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       (T"symbol" "regexp" [] -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])))),
   V"i" (T"list" "list" [T"item" "parserDef" []]),
   V"itl" (T"list" "list" [T"list" "list" [T"item" "parserDef" []]]),
   C"LET" "bool"
    (((T"list" "list" [T"item" "parserDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]) -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]))),
   C"LET" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]) -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]))),
   C"pair_case" "pair"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])) -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] -->
       T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]]))),
   C"list_case" "list"
    ((T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]] -->
      ((T"item" "parserDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] -->
         T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]])) -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])))),
   C"list_case" "list"
    ((T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])))),
   V"v5" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v9" (T"list" "list" [T"rule" "grammarDef" []]),
   C"slrML" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"list" "list" [T"item" "parserDef" []]] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]])))),
   V"rst" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min"
    (((T"prod" "pair"
        [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> bool) -->
      ((T"prod" "pair"
         [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool) --> bool))),
   C"findItemInRules_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) -->
      (((T"prod" "pair"
          [T"item" "parserDef" [],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool) -->
        (T"prod" "pair"
          [T"item" "parserDef" [],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool)) -->
       (T"prod" "pair"
         [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
        -->
        (T"prod" "pair"
          [T"item" "parserDef" [],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
      -->
      (T"prod" "pair"
        [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
       -->
       (T"prod" "pair"
         [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
        --> bool)) --> bool)),
   V"findItemInRules_tupled"
    ((T"prod" "pair"
       [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
      --> bool)),
   V"a"
    (T"prod" "pair"
      [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]),
   C"pair_case" "pair"
    (((T"item" "parserDef" [] -->
       (T"list" "list" [T"rule" "grammarDef" []] --> bool)) -->
      (T"prod" "pair"
        [T"item" "parserDef" [], T"list" "list" [T"rule" "grammarDef" []]]
       --> bool))), V"v" (T"item" "parserDef" []),
   V"l1" (T"string" "string" []),
   C"list_case" "list"
    ((bool -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   V"v18" (T"rule" "grammarDef" []),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
      (T"rule" "grammarDef" [] --> bool))), V"l2" (T"string" "string" []),
   V"v14" (T"symbol" "regexp" []),
   V"v15" (T"list" "list" [T"symbol" "regexp" []]),
   V"x" (T"item" "parserDef" []),
   C"findItemInRules" "yaccDef"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"," "pair"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"item" "parserDef" [],
         T"list" "list" [T"rule" "grammarDef" []]]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] --> bool) -->
      ((T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []],
          T"list" "list" [T"rule" "grammarDef" []]] --> bool) --> bool))),
   C"itemEqRuleList_defn_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"list" "list" [T"item" "parserDef" []],
        T"list" "list" [T"rule" "grammarDef" []]] --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []],
          T"list" "list" [T"rule" "grammarDef" []]] --> bool)) -->
      (((T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool) -->
        (T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool)) -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []],
          T"list" "list" [T"rule" "grammarDef" []]] --> bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []],
          T"list" "list" [T"rule" "grammarDef" []]] -->
        (T"prod" "pair"
          [T"list" "list" [T"item" "parserDef" []],
           T"list" "list" [T"rule" "grammarDef" []]] --> bool)) --> bool)
      -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []],
          T"list" "list" [T"rule" "grammarDef" []]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"list" "list" [T"item" "parserDef" []],
        T"list" "list" [T"rule" "grammarDef" []]] -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] -->
       (T"prod" "pair"
         [T"list" "list" [T"item" "parserDef" []],
          T"list" "list" [T"rule" "grammarDef" []]] --> bool)) --> bool)),
   V"v16" (T"list" "list" [T"rule" "grammarDef" []]),
   C"!" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   V"v15" (T"rule" "grammarDef" []),
   V"v6" (T"list" "list" [T"item" "parserDef" []]),
   V"v5" (T"item" "parserDef" []),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"LENGTH" "list"
    ((T"list" "list" [T"item" "parserDef" []] --> T"num" "num" [])),
   C"LENGTH" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] --> T"num" "num" [])),
   C"HD" "list"
    ((T"list" "list" [T"item" "parserDef" []] --> T"item" "parserDef" [])),
   C"TL" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      T"list" "list" [T"item" "parserDef" []])),
   V"itemEqRuleList_defn_tupled"
    ((T"prod" "pair"
       [T"list" "list" [T"item" "parserDef" []],
        T"list" "list" [T"rule" "grammarDef" []]] --> bool)),
   V"a"
    (T"prod" "pair"
      [T"list" "list" [T"item" "parserDef" []],
       T"list" "list" [T"rule" "grammarDef" []]]),
   V"v2" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v13" (T"rule" "grammarDef" []),
   V"v14" (T"list" "list" [T"rule" "grammarDef" []]),
   V"v7" (T"item" "parserDef" []),
   V"v8" (T"list" "list" [T"item" "parserDef" []]),
   V"v17" (T"rule" "grammarDef" []),
   V"v18" (T"list" "list" [T"rule" "grammarDef" []]),
   C"COND" "bool" ((bool --> (bool --> (bool --> bool)))),
   C"itemEqRuleList" "yaccDef"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"!" "bool"
    ((((T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])) --> bool) --> bool)),
   C"!" "bool"
    ((((T"list" "list" [T"item" "parserDef" []] -->
        (T"string" "string" [] -->
         T"list" "list" [T"rule" "grammarDef" []])) --> bool) --> bool)),
   C"=" "min"
    ((T"action" "parserDef" [] --> (T"action" "parserDef" [] --> bool))),
   C"getState" "yaccDef"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])),
        (T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []]))] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] --> T"action" "parserDef" [])))),
   C"LET" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] -->
       T"action" "parserDef" []) -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"action" "parserDef" []))),
   C"LET" "bool"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"action" "parserDef" [])) -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"action" "parserDef" [])))),
   V"newitl" (T"list" "list" [T"item" "parserDef" []]),
   V"rl" (T"list" "list" [T"rule" "grammarDef" []]),
   C"pair_case" "pair"
    (((T"list" "list" [T"item" "parserDef" []] -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"action" "parserDef" [])) -->
      (T"prod" "pair"
        [T"list" "list" [T"item" "parserDef" []],
         T"list" "list" [T"rule" "grammarDef" []]] -->
       T"action" "parserDef" []))),
   C"list_case" "list"
    ((T"action" "parserDef" [] -->
      ((T"item" "parserDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] -->
         T"action" "parserDef" [])) -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"action" "parserDef" [])))),
   C"list_case" "list"
    ((T"action" "parserDef" [] -->
      ((T"rule" "grammarDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] -->
         T"action" "parserDef" [])) -->
       (T"list" "list" [T"rule" "grammarDef" []] -->
        T"action" "parserDef" [])))),
   C"NA" "parserDef" (T"action" "parserDef" []),
   V"y" (T"rule" "grammarDef" []),
   V"ys" (T"list" "list" [T"rule" "grammarDef" []]),
   C"COND" "bool"
    ((bool -->
      (T"action" "parserDef" [] -->
       (T"action" "parserDef" [] --> T"action" "parserDef" [])))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"REDUCE" "parserDef"
    ((T"rule" "grammarDef" [] --> T"action" "parserDef" [])),
   C"HD" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      T"rule" "grammarDef" [])),
   V"xs" (T"list" "list" [T"item" "parserDef" []]),
   C"GOTO" "parserDef"
    ((T"state" "parserDef" [] --> T"action" "parserDef" [])),
   V"y'" (T"rule" "grammarDef" []),
   V"ys'" (T"list" "list" [T"rule" "grammarDef" []]),
   C"=" "min"
    (((T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      ((T"prod" "pair"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])), alpha],
          T"prod" "pair"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]],
            T"rule" "grammarDef" []]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]]) --> bool))),
   C"doReduce_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])), alpha],
        T"prod" "pair"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]],
          T"rule" "grammarDef" []]] -->
      T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])), alpha],
          T"prod" "pair"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]],
            T"rule" "grammarDef" []]] --> bool)) -->
      (((T"prod" "pair"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])), alpha],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"prod" "pair"
                [T"list" "list"
                  [T"prod" "pair"
                    [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                 T"list" "list" [T"state" "parserDef" []]]],
             T"rule" "grammarDef" []]] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]) -->
        (T"prod" "pair"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])), alpha],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"prod" "pair"
                [T"list" "list"
                  [T"prod" "pair"
                    [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                 T"list" "list" [T"state" "parserDef" []]]],
             T"rule" "grammarDef" []]] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]])) -->
       (T"prod" "pair"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])), alpha],
          T"prod" "pair"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]],
            T"rule" "grammarDef" []]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])), alpha],
          T"prod" "pair"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]],
            T"rule" "grammarDef" []]] -->
        (T"prod" "pair"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])), alpha],
           T"prod" "pair"
            [T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"prod" "pair"
                [T"list" "list"
                  [T"prod" "pair"
                    [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                 T"list" "list" [T"state" "parserDef" []]]],
             T"rule" "grammarDef" []]] --> bool)) --> bool) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])), alpha],
          T"prod" "pair"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]],
            T"rule" "grammarDef" []]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])), alpha],
        T"prod" "pair"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]],
          T"rule" "grammarDef" []]] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])), alpha],
          T"prod" "pair"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]],
            T"rule" "grammarDef" []]] --> bool)) --> bool)),
   V"doReduce_tupled"
    ((T"prod" "pair"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])), alpha],
        T"prod" "pair"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]],
          T"rule" "grammarDef" []]] -->
      T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]])),
   V"a"
    (T"prod" "pair"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])), alpha],
       T"prod" "pair"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]],
         T"rule" "grammarDef" []]]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])), alpha] -->
       (T"prod" "pair"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]],
          T"rule" "grammarDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"m"
    (T"prod" "pair"
      [(T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])), alpha]),
   V"v1"
    (T"prod" "pair"
      [T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]],
       T"rule" "grammarDef" []]),
   C"pair_case" "pair"
    (((T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       (T"rule" "grammarDef" [] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]],
         T"rule" "grammarDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"v2"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]]]),
   V"ru" (T"rule" "grammarDef" []),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"prod" "pair"
         [T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]],
          T"list" "list" [T"state" "parserDef" []]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"v4" (T"list" "list" [T"symbol" "regexp" []]),
   V"v5"
    (T"prod" "pair"
      [T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]],
       T"list" "list" [T"state" "parserDef" []]]),
   C"list_case" "list"
    ((T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]])) -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   C"ARB" "bool"
    (T"option" "option"
      [T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]]]),
   C"pair_case" "pair"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list" [T"state" "parserDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"os"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"v11" (T"list" "list" [T"state" "parserDef" []]),
   C"list_case" "list"
    ((T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      ((T"state" "parserDef" [] -->
        (T"list" "list" [T"state" "parserDef" []] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]])) -->
       (T"list" "list" [T"state" "parserDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   V"v12" (T"state" "parserDef" []),
   V"rem" (T"list" "list" [T"state" "parserDef" []]),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"state" "parserDef" [] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   C"I" "combin"
    ((T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]])),
   C"COND" "bool"
    ((bool -->
      (T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] -->
       (T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   C"isNonTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   C"NONE" "option"
    (T"option" "option"
      [T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]]]),
   C"LET" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   C"LET" "bool"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   C"LET" "bool"
    (((T"option" "option" [T"ptree" "parseTree" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"option" "option" [T"ptree" "parseTree" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"ptree" (T"option" "option" [T"ptree" "parseTree" []]),
   C"option_case" "option"
    ((T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      ((T"ptree" "parseTree" [] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]]) -->
       (T"option" "option" [T"ptree" "parseTree" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   V"p" (T"ptree" "parseTree" []),
   C"LET" "bool"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"newStk"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"LET" "bool"
    (((T"list" "list" [T"state" "parserDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"list" "list" [T"state" "parserDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"newStateStk" (T"list" "list" [T"state" "parserDef" []]),
   C"=" "min"
    ((T"list" "list" [T"state" "parserDef" []] -->
      (T"list" "list" [T"state" "parserDef" []] --> bool))),
   C"NIL" "list" (T"list" "list" [T"state" "parserDef" []]),
   C"LET" "bool"
    (((T"list" "list" [T"item" "parserDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"topitl" (T"list" "list" [T"item" "parserDef" []]),
   C"LET" "bool"
    (((T"state" "parserDef" [] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"state" "parserDef" [] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"ns" (T"state" "parserDef" []),
   C"SOME" "option"
    ((T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"prod" "pair"
         [T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]],
          T"list" "list" [T"state" "parserDef" []]]] -->
      T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]])),
   C"," "pair"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]] -->
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]]))),
   C"," "pair"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"list" "list" [T"state" "parserDef" []] -->
       T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]]))),
   C"APPEND" "list"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]]))),
   C"CONS" "list"
    ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []] -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]]))),
   C"," "pair"
    ((T"state" "parserDef" [] -->
      (T"ptree" "parseTree" [] -->
       T"prod" "pair"
        [T"state" "parserDef" [], T"ptree" "parseTree" []]))),
   C"NIL" "list"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"push" "listLemmas"
    ((T"list" "list" [T"state" "parserDef" []] -->
      (T"state" "parserDef" [] -->
       T"list" "list" [T"state" "parserDef" []]))),
   C"FST" "pair"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])), alpha] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] -->
        T"list" "list" [T"item" "parserDef" []])))),
   C"stateItl" "parserDef"
    ((T"state" "parserDef" [] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"HD" "list"
    ((T"list" "list" [T"state" "parserDef" []] -->
      T"state" "parserDef" [])),
   C"pop" "listLemmas"
    ((T"list" "list" [T"state" "parserDef" []] -->
      (T"num" "num" [] --> T"list" "list" [T"state" "parserDef" []]))),
   C"pop" "listLemmas"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"num" "num" [] -->
       T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]]))),
   C"addRule" "yaccDef"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"rule" "grammarDef" [] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   C"ruleLhs" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"string" "string" [])),
   C"ruleRhs" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"!" "bool"
    (((T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])), alpha] --> bool) -->
      bool)),
   V"x"
    (T"prod" "pair"
      [(T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])), alpha]),
   C"!" "bool"
    (((T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] --> bool) --> bool)),
   V"x1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]]]),
   V"x2" (T"rule" "grammarDef" []),
   C"=" "min"
    ((T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      (T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] --> bool))),
   C"doReduce" "yaccDef"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])), alpha] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       (T"rule" "grammarDef" [] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   C"," "pair"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])), alpha] -->
      (T"prod" "pair"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]],
         T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])), alpha],
         T"prod" "pair"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]],
           T"rule" "grammarDef" []]]))),
   C"," "pair"
    ((T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"prod" "pair"
         [T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]],
          T"list" "list" [T"state" "parserDef" []]]] -->
      (T"rule" "grammarDef" [] -->
       T"prod" "pair"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]],
         T"rule" "grammarDef" []]))),
   C"=" "min"
    (((T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      ((T"prod" "pair"
         [T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]]) --> bool))),
   C"parse_tupled" "yaccDef"
    ((T"prod" "pair"
       [T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]])),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] -->
       (T"prod" "pair"
         [T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] --> bool)) -->
      (((T"prod" "pair"
          [T"option" "option"
            [T"prod" "pair"
              [(T"list" "list" [T"item" "parserDef" []] -->
                (T"symbol" "regexp" [] -->
                 T"list" "list" [T"item" "parserDef" []])),
               (T"list" "list" [T"item" "parserDef" []] -->
                (T"string" "string" [] -->
                 T"list" "list" [T"rule" "grammarDef" []]))]],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]) -->
        (T"prod" "pair"
          [T"option" "option"
            [T"prod" "pair"
              [(T"list" "list" [T"item" "parserDef" []] -->
                (T"symbol" "regexp" [] -->
                 T"list" "list" [T"item" "parserDef" []])),
               (T"list" "list" [T"item" "parserDef" []] -->
                (T"string" "string" [] -->
                 T"list" "list" [T"rule" "grammarDef" []]))]],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]])) -->
       (T"prod" "pair"
         [T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        (T"prod" "pair"
          [T"option" "option"
            [T"prod" "pair"
              [(T"list" "list" [T"item" "parserDef" []] -->
                (T"symbol" "regexp" [] -->
                 T"list" "list" [T"item" "parserDef" []])),
               (T"list" "list" [T"item" "parserDef" []] -->
                (T"string" "string" [] -->
                 T"list" "list" [T"rule" "grammarDef" []]))]],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]] --> bool)) -->
       bool) -->
      (T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] -->
       (T"prod" "pair"
         [T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] --> bool)))),
   V"R"
    ((T"prod" "pair"
       [T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      (T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] -->
       (T"prod" "pair"
         [T"option" "option"
           [T"prod" "pair"
             [(T"list" "list" [T"item" "parserDef" []] -->
               (T"symbol" "regexp" [] -->
                T"list" "list" [T"item" "parserDef" []])),
              (T"list" "list" [T"item" "parserDef" []] -->
               (T"string" "string" [] -->
                T"list" "list" [T"rule" "grammarDef" []]))]],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] --> bool)) -->
      bool)),
   V"parse_tupled"
    ((T"prod" "pair"
       [T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]])),
   V"a"
    (T"prod" "pair"
      [T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]],
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]]]),
   C"pair_case" "pair"
    (((T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"mac"
    (T"option" "option"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]]),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]]]),
   V"inp" (T"list" "list" [T"symbol" "regexp" []]),
   V"v3"
    (T"prod" "pair"
      [T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]],
       T"list" "list" [T"state" "parserDef" []]]),
   V"v5" (T"list" "list" [T"state" "parserDef" []]),
   V"v6" (T"state" "parserDef" []),
   C"option_case" "option"
    ((T"option" "option"
       [T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]]] -->
      ((T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]]) -->
       (T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   V"m"
    (T"prod" "pair"
      [(T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])),
       (T"list" "list" [T"item" "parserDef" []] -->
        (T"string" "string" [] -->
         T"list" "list" [T"rule" "grammarDef" []]))]),
   V"e" (T"symbol" "regexp" []),
   V"v1" (T"list" "list" [T"symbol" "regexp" []]),
   C"LET" "bool"
    (((T"action" "parserDef" [] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      (T"action" "parserDef" [] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"newState" (T"action" "parserDef" []),
   C"action_case" "parserDef"
    (((T"rule" "grammarDef" [] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]) -->
      ((T"state" "parserDef" [] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]]) -->
       (T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        (T"action" "parserDef" [] -->
         T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]))))),
   C"doReduce" "yaccDef"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])),
        (T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] -->
          T"list" "list" [T"rule" "grammarDef" []]))] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       (T"rule" "grammarDef" [] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])))),
   V"st" (T"state" "parserDef" []), V"v4" (T"symbol" "regexp" []),
   V"v5" (T"list" "list" [T"symbol" "regexp" []]),
   C"Leaf" "parseTree"
    ((T"terminal" "parseTree" [] --> T"ptree" "parseTree" [])),
   C"TM" "parseTree"
    ((T"string" "string" [] --> T"terminal" "parseTree" [])),
   C"tmnlSym" "regexp" ((T"symbol" "regexp" [] --> T"string" "string" [])),
   C"!" "bool"
    (((T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] --> bool) -->
      bool)),
   V"x"
    (T"option" "option"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]]),
   C"parse" "yaccDef"
    ((T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   C"," "pair"
    ((T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       T"prod" "pair"
        [T"option" "option"
          [T"prod" "pair"
            [(T"list" "list" [T"item" "parserDef" []] -->
              (T"symbol" "regexp" [] -->
               T"list" "list" [T"item" "parserDef" []])),
             (T"list" "list" [T"item" "parserDef" []] -->
              (T"string" "string" [] -->
               T"list" "list" [T"rule" "grammarDef" []]))]],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"m"
    (T"option" "option"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]]),
   V"sl" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool) --> bool)),
   V"stl"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"curStatel" (T"list" "list" [T"state" "parserDef" []]),
   V"eof" (T"symbol" "regexp" []), V"oldsym" (T"symbol" "regexp" []),
   C"=" "min"
    ((T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]] -->
      (T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]]
       --> bool))),
   C"parser" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         (T"list" "list" [T"state" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           (T"symbol" "regexp" [] -->
            T"option" "option"
             [T"option" "option" [T"ptree" "parseTree" []]])))))))),
   C"LET" "bool"
    (((T"option" "option"
        [T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]] -->
       T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]])
      -->
      (T"option" "option"
        [T"option" "option"
          [T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"list" "list"
                [T"prod" "pair"
                  [T"state" "parserDef" [], T"ptree" "parseTree" []]],
               T"list" "list" [T"state" "parserDef" []]]]]] -->
       T"option" "option"
        [T"option" "option" [T"ptree" "parseTree" []]]))),
   V"out"
    (T"option" "option"
      [T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]]),
   C"option_case" "option"
    ((T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]] -->
      ((T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]])
       -->
       (T"option" "option"
         [T"option" "option"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]]]] -->
        T"option" "option"
         [T"option" "option" [T"ptree" "parseTree" []]])))),
   C"NONE" "option"
    (T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]]),
   V"v"
    (T"option" "option"
      [T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]]]),
   C"option_case" "option"
    ((T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]] -->
      ((T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]] -->
        T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]])
       -->
       (T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        T"option" "option"
         [T"option" "option" [T"ptree" "parseTree" []]])))),
   C"SOME" "option"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]])),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"prod" "pair"
         [T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]],
          T"list" "list" [T"state" "parserDef" []]] -->
        T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]]))
      -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       T"option" "option"
        [T"option" "option" [T"ptree" "parseTree" []]]))),
   V"slo" (T"list" "list" [T"symbol" "regexp" []]),
   V"v6"
    (T"prod" "pair"
      [T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]],
       T"list" "list" [T"state" "parserDef" []]]),
   C"pair_case" "pair"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list" [T"state" "parserDef" []] -->
        T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]]))
      -->
      (T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]] -->
       T"option" "option"
        [T"option" "option" [T"ptree" "parseTree" []]]))),
   V"v9"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"cs" (T"list" "list" [T"state" "parserDef" []]),
   C"list_case" "list"
    ((T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]] -->
      ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
        -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         T"option" "option"
          [T"option" "option" [T"ptree" "parseTree" []]])) -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        T"option" "option"
         [T"option" "option" [T"ptree" "parseTree" []]])))),
   V"v13"
    (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]),
   V"v14"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"pair_case" "pair"
    (((T"state" "parserDef" [] -->
       (T"ptree" "parseTree" [] -->
        T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]]))
      -->
      (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
       -->
       T"option" "option"
        [T"option" "option" [T"ptree" "parseTree" []]]))),
   V"st1" (T"state" "parserDef" []), V"pt" (T"ptree" "parseTree" []),
   C"APPEND" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"CONS" "list"
    ((T"ptree" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"NIL" "list" (T"list" "list" [T"ptree" "parseTree" []]),
   V"v21"
    (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]),
   V"v22"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"mwhile" "whileLemmas"
    (((T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] --> bool) -->
      ((T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair"
           [T"list" "list"
             [T"prod" "pair"
               [T"state" "parserDef" [], T"ptree" "parseTree" []]],
            T"list" "list" [T"state" "parserDef" []]]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]]) -->
       (T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]] -->
        T"option" "option"
         [T"option" "option"
           [T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"prod" "pair"
               [T"list" "list"
                 [T"prod" "pair"
                   [T"state" "parserDef" [], T"ptree" "parseTree" []]],
                T"list" "list" [T"state" "parserDef" []]]]]])))),
   C"UNCURRY" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"prod" "pair"
         [T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]],
          T"list" "list" [T"state" "parserDef" []]] --> bool)) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] --> bool))),
   V"sli" (T"list" "list" [T"symbol" "regexp" []]),
   C"UNCURRY" "pair"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> (T"list" "list" [T"state" "parserDef" []] --> bool)) -->
      (T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]] --> bool))),
   V"stli"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"csli" (T"list" "list" [T"state" "parserDef" []]),
   C"stateSym" "parserDef"
    ((T"state" "parserDef" [] --> T"symbol" "regexp" [])),
   C"FST" "pair"
    ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []] -->
      T"state" "parserDef" [])),
   C"HD" "list"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []])),
   C"UNCURRY" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"prod" "pair"
         [T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]],
          T"list" "list" [T"state" "parserDef" []]] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   C"UNCURRY" "pair"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list" [T"state" "parserDef" []] -->
        T"option" "option"
         [T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"list" "list"
               [T"prod" "pair"
                 [T"state" "parserDef" [], T"ptree" "parseTree" []]],
              T"list" "list" [T"state" "parserDef" []]]]])) -->
      (T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]] -->
       T"option" "option"
        [T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"s'" (T"string" "string" []),
   C"yacc" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"string" "string" [] -->
       (T"string" "string" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"option" "option" [T"ptree" "parseTree" []]))))),
   C"LET" "bool"
    (((T"option" "option" [T"grammar" "grammarDef" []] -->
       T"option" "option" [T"ptree" "parseTree" []]) -->
      (T"option" "option" [T"grammar" "grammarDef" []] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   V"g'" (T"option" "option" [T"grammar" "grammarDef" []]),
   C"option_case" "option"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      ((T"grammar" "grammarDef" [] -->
        T"option" "option" [T"ptree" "parseTree" []]) -->
       (T"option" "option" [T"grammar" "grammarDef" []] -->
        T"option" "option" [T"ptree" "parseTree" []])))),
   V"ag" (T"grammar" "grammarDef" []),
   C"LET" "bool"
    (((T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] -->
       T"option" "option" [T"ptree" "parseTree" []]) -->
      (T"option" "option"
        [T"prod" "pair"
          [(T"list" "list" [T"item" "parserDef" []] -->
            (T"symbol" "regexp" [] -->
             T"list" "list" [T"item" "parserDef" []])),
           (T"list" "list" [T"item" "parserDef" []] -->
            (T"string" "string" [] -->
             T"list" "list" [T"rule" "grammarDef" []]))]] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   C"option_case" "option"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      ((T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))] -->
        T"option" "option" [T"ptree" "parseTree" []]) -->
       (T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]] -->
        T"option" "option" [T"ptree" "parseTree" []])))),
   C"LET" "bool"
    (((T"state" "parserDef" [] -->
       T"option" "option" [T"ptree" "parseTree" []]) -->
      (T"state" "parserDef" [] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   V"initState" (T"state" "parserDef" []),
   C"option_case" "option"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      ((T"option" "option" [T"ptree" "parseTree" []] -->
        T"option" "option" [T"ptree" "parseTree" []]) -->
       (T"option" "option" [T"option" "option" [T"ptree" "parseTree" []]]
        --> T"option" "option" [T"ptree" "parseTree" []])))),
   V"v" (T"option" "option" [T"ptree" "parseTree" []]),
   C"option_case" "option"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      ((T"ptree" "parseTree" [] -->
        T"option" "option" [T"ptree" "parseTree" []]) -->
       (T"option" "option" [T"ptree" "parseTree" []] -->
        T"option" "option" [T"ptree" "parseTree" []])))),
   V"out" (T"ptree" "parseTree" []),
   C"!" "bool"
    ((((T"list" "list" [T"rule" "grammarDef" []] -->
        (T"string" "string" [] --> bool)) --> bool) --> bool)),
   V"P"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"string" "string" [] --> bool))), V"v1" (T"string" "string" []),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] --> bool)) --> bool) -->
      bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   V"v" (T"grammar" "grammarDef" []),
   C"!" "bool"
    ((((T"list" "list" [T"rule" "grammarDef" []] --> bool) --> bool) -->
      bool)), V"P" ((T"list" "list" [T"rule" "grammarDef" []] --> bool)),
   V"e" (T"item" "parserDef" []),
   V"l" (T"list" "list" [T"item" "parserDef" []]),
   C"MEM" "list"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C">=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"lhs" (T"string" "string" []),
   C">" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"CARD" "pred_set"
    (((T"item" "parserDef" [] --> bool) --> T"num" "num" [])),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"INTER" "pred_set"
    (((T"item" "parserDef" [] --> bool) -->
      ((T"item" "parserDef" [] --> bool) -->
       (T"item" "parserDef" [] --> bool)))), C"0" "num" (T"num" "num" []),
   C"!" "bool"
    ((((T"string" "string" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> bool)) --> bool) -->
      bool)),
   V"P"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   V"v" (T"string" "string" []),
   C"!" "bool"
    ((((T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] --> bool)) --> bool) --> bool)),
   V"P"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"symbol" "regexp" [] --> bool))), V"v1" (T"symbol" "regexp" []),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list" [T"state" "parserDef" []] --> bool)) --> bool) -->
      bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"state" "parserDef" []] --> bool))),
   V"l1" (T"list" "list" [T"item" "parserDef" []]),
   V"l2" (T"list" "list" [T"item" "parserDef" []]),
   V"l1" (T"list" "list" [T"state" "parserDef" []]),
   V"l2" (T"list" "list" [T"state" "parserDef" []]),
   C"APPEND" "list"
    ((T"list" "list" [T"state" "parserDef" []] -->
      (T"list" "list" [T"state" "parserDef" []] -->
       T"list" "list" [T"state" "parserDef" []]))),
   V"l" (T"list" "list" [T"state" "parserDef" []]),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"n" (T"num" "num" []), V"e" (T"rule" "grammarDef" []),
   V"sym" (T"string" "string" []),
   V"t" (T"list" "list" [T"item" "parserDef" []]),
   V"h" (T"item" "parserDef" []),
   C"delete" "listLemmas"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list" [T"item" "parserDef" []] -->
         (T"string" "string" [] --> bool))) --> bool) --> bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"string" "string" [] --> bool)))), V"v2" (T"string" "string" []),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] --> (T"item" "parserDef" [] --> bool))
       --> bool) --> bool)),
   V"P"
    ((T"grammar" "grammarDef" [] --> (T"item" "parserDef" [] --> bool))),
   C"FINITE" "pred_set" (((T"item" "parserDef" [] --> bool) --> bool)),
   C"GSPEC" "pred_set"
    (((T"item" "parserDef" [] -->
       T"prod" "pair" [T"item" "parserDef" [], bool]) -->
      (T"item" "parserDef" [] --> bool))), V"i" (T"item" "parserDef" []),
   C"," "pair"
    ((T"item" "parserDef" [] -->
      (bool --> T"prod" "pair" [T"item" "parserDef" [], bool]))),
   C"=" "min"
    (((T"rule" "grammarDef" [] --> bool) -->
      ((T"rule" "grammarDef" [] --> bool) --> bool))),
   C"GSPEC" "pred_set"
    (((T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       T"prod" "pair" [T"rule" "grammarDef" [], bool]) -->
      (T"rule" "grammarDef" [] --> bool))),
   C"UNCURRY" "pair"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] -->
        T"prod" "pair" [T"rule" "grammarDef" [], bool])) -->
      (T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       T"prod" "pair" [T"rule" "grammarDef" [], bool]))),
   C"UNCURRY" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"prod" "pair" [T"rule" "grammarDef" [], bool])) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"prod" "pair" [T"rule" "grammarDef" [], bool]))),
   C"," "pair"
    ((T"rule" "grammarDef" [] -->
      (bool --> T"prod" "pair" [T"rule" "grammarDef" [], bool]))),
   C"LIST_TO_SET" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"rule" "grammarDef" [] --> bool))),
   V"l1" (T"list" "list" [T"rule" "grammarDef" []]),
   V"l2" (T"list" "list" [T"rule" "grammarDef" []]),
   V"it" (T"item" "parserDef" []),
   V"q" (T"list" "list" [T"symbol" "regexp" []]),
   C"FINITE" "pred_set"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   C"!" "bool" (((alpha --> bool) --> bool)), V"P" (alpha),
   V"l" (T"list" "list" [T"symbol" "regexp" []]),
   V"e" (T"list" "list" [T"item" "parserDef" []]),
   V"e'" (T"symbol" "regexp" []),
   C"MEM" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   V"a" (T"num" "num" []), V"b" (T"num" "num" []), V"c" (T"num" "num" []),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"!" "bool"
    ((((T"item" "parserDef" [] -->
        (T"list" "list" [T"rule" "grammarDef" []] --> bool)) --> bool) -->
      bool)),
   V"P"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"!" "bool"
    ((((T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])), alpha] -->
        (T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]] -->
         (T"rule" "grammarDef" [] --> bool))) --> bool) --> bool)),
   V"P"
    ((T"prod" "pair"
       [(T"list" "list" [T"item" "parserDef" []] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"item" "parserDef" []])), alpha] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] -->
       (T"rule" "grammarDef" [] --> bool)))),
   V"v14" (T"rule" "grammarDef" []),
   C"!" "bool"
    (((T"prod" "pair"
        [T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]],
         T"list" "list" [T"state" "parserDef" []]] --> bool) --> bool)),
   V"v8"
    (T"prod" "pair"
      [T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]],
       T"list" "list" [T"state" "parserDef" []]]),
   V"v9" (T"rule" "grammarDef" []),
   V"v"
    (T"prod" "pair"
      [(T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])), alpha]),
   V"v2"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"v3" (T"list" "list" [T"state" "parserDef" []]),
   V"v4" (T"rule" "grammarDef" []),
   C"!" "bool"
    ((((T"option" "option"
         [T"prod" "pair"
           [(T"list" "list" [T"item" "parserDef" []] -->
             (T"symbol" "regexp" [] -->
              T"list" "list" [T"item" "parserDef" []])),
            (T"list" "list" [T"item" "parserDef" []] -->
             (T"string" "string" [] -->
              T"list" "list" [T"rule" "grammarDef" []]))]] -->
        (T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"list" "list"
              [T"prod" "pair"
                [T"state" "parserDef" [], T"ptree" "parseTree" []]],
             T"list" "list" [T"state" "parserDef" []]]] --> bool)) -->
       bool) --> bool)),
   V"P"
    ((T"option" "option"
       [T"prod" "pair"
         [(T"list" "list" [T"item" "parserDef" []] -->
           (T"symbol" "regexp" [] -->
            T"list" "list" [T"item" "parserDef" []])),
          (T"list" "list" [T"item" "parserDef" []] -->
           (T"string" "string" [] -->
            T"list" "list" [T"rule" "grammarDef" []]))]] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]],
           T"list" "list" [T"state" "parserDef" []]]] --> bool))),
   V"v"
    (T"option" "option"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]])]
  val DT = Thm.disk_thm share_table
  in
  val getItems_tupled_primitive_def =
    DT([], [],
       `((%0 %1) ((%2 (%3 (\%4. ((%5 (%6 $0)) ((%5 (%7 (\%8. (%9 (\%10.
       (%11 (\%12. (%11 (\%13. ((%14 (%15 ((%16 $0) $1))) (($4 ((%17 $2)
       $1)) ((%17 ((%18 ((%19 $0) $3)) $2)) $1)))))))))))) (%7 (\%8. (%9
       (\%10. (%11 (\%12. (%11 (\%13. ((%14 ((%16 $0) $1)) (($4 ((%17 $2)
       $1)) ((%17 ((%18 ((%19 $0) $3)) $2)) $1)))))))))))))))) (\%20.
       (\%21. ((%22 (\%23. (\%12. (((%24 (%25 %26)) (\%27. (\%10. ((%28
       (\%13. (\%8. (%25 (((%29 ((%16 $1) $4)) ((%30 ((%31 $1) ((%32 %33)
       $0))) ($7 ((%17 $2) $4)))) ($7 ((%17 $2) $4))))))) $1)))) $1))))
       $0)))))`)
  val getItems_curried_def =
    DT([], [],
       `(%9 (\%34. (%11 (\%35. ((%36 ((%37 $1) $0)) (%1 ((%17 $1)
       $0)))))))`)
  val iclosure1_tupled_primitive_def =
    DT([], [],
       `((%38 %39) ((%40 (%41 (\%42. ((%5 (%43 $0)) ((%5 (%7 (\%44. (%11
       (\%12. (%45 (\%46. (%47 (\%48. (($4 ((%49 $0) $1)) ((%49 $0) ((%30
       ((%31 $2) ((%32 $3) %33))) $1)))))))))))) ((%5 (%7 (\%50. (%11
       (\%51. (%7 (\%44. (%11 (\%12. (%45 (\%46. (%47 (\%48. (($6 ((%49 $0)
       $1)) ((%49 $0) ((%30 ((%31 $2) ((%32 $3) ((%52 (%53 $4)) $5))))
       $1)))))))))))))))) (%7 (\%50. (%11 (\%54. (%7 (\%44. (%11 (\%12.
       (%45 (\%46. (%47 (\%48. (($6 ((%49 $0) $1)) ((%49 $0) ((%30 ((%31
       $2) ((%32 $3) ((%52 (%55 $4)) $5)))) $1))))))))))))))))))))) (\%56.
       (\%57. ((%58 (\%48. (\%59. (((%60 (%25 %26)) (\%61. (\%46. ((%62
       (\%12. (\%63. ((%64 (\%44. (\%65. (((%66 (%25 ((%30 ((%31 $3) ((%32
       $1) %33))) ($9 ((%49 $7) $4))))) (\%67. (\%50. (((%68 (\%51. (%25
       ((%30 ((%31 $6) ((%32 $4) ((%52 (%53 $0)) $1)))) ($12 ((%49 $10)
       $7)))))) (\%54. (%25 ((%69 ((%69 ((%37 (%70 $10)) $0)) ((%30 ((%31
       $6) ((%32 $4) ((%52 (%55 $0)) $1)))) %26))) ($12 ((%49 $10) $7))))))
       $1)))) $0)))) $0)))) $1)))) $0)))) $0)))))`)
  val iclosure1_curried_def =
    DT([], [],
       `(%47 (\%71. (%45 (\%72. ((%36 ((%73 $1) $0)) (%39 ((%49 $1)
       $0)))))))`)
  val iclosure_defn_tupled_primitive_def =
    DT([], [],
       `((%38 %74) ((%40 (%41 (\%42. ((%5 (%43 $0)) (%47 (\%48. (%45 (\%75.
       (%76 (\%61. (%45 (\%77. (%45 (\%78. ((%14 ((%5 ((%36 $1) (%79 ((%30
       $2) $3)))) ((%5 ((%36 $0) (%79 ((%73 $4) $1)))) (%15 ((%80 (%81 $1))
       (%81 $0)))))) (($5 ((%49 $4) $0)) ((%49 $4) ((%30 $2)
       $3)))))))))))))))))) (\%82. (\%57. ((%58 (\%48. (\%59. (((%60 (%25
       %26)) (\%83. (\%84. (%25 ((%85 (\%77. ((%85 (\%78. (((%29 (%15 ((%80
       (%81 $1)) (%81 $0)))) ($7 ((%49 $5) $0))) $0))) (%79 ((%73 $4)
       $0))))) (%79 ((%30 $1) $0))))))) $0)))) $0)))))`)
  val iclosure_defn_curried_def =
    DT([], [],
       `(%47 (\%71. (%45 (\%72. ((%36 ((%86 $1) $0)) (%74 ((%49 $1)
       $0)))))))`)
  val rules2Items_primitive_def =
    DT([], [],
       `((%87 %88) ((%89 (%90 (\%91. ((%5 (%92 $0)) (%7 (\%8. (%11 (\%13.
       (%9 (\%93. (($3 $0) ((%18 ((%19 $1) $2)) $0)))))))))))) (\%94.
       (\%95. (((%24 (%25 %26)) (\%96. (\%93. ((%28 (\%13. (\%8. (%25 ((%30
       ((%31 $1) ((%32 %33) $0))) ($5 $2)))))) $1)))) $0)))))`)
  val auggr_def =
    DT([], [],
       `(%47 (\%48. (%11 (\%12. (%11 (\%97. ((%98 (((%99 $2) $1) $0))
       (((%100 ((%5 (%15 ((%101 (%55 $1)) (%102 $2)))) (%15 ((%101 (%53
       $0)) (%102 $2))))) (%103 ((%104 ((%105 ((%18 ((%19 $1) ((%52 (%55
       (%106 $2))) ((%52 (%53 $0)) %33)))) %107)) (%70 $2))) $1)))
       %108))))))))`)
  val initProds2Items_tupled_primitive_def =
    DT([], [],
       `((%109 %110) ((%111 (%112 (\%113. ((%5 (%114 $0)) ((%5 (%7 (\%8.
       (%9 (\%10. (%11 (\%13. (%11 (\%12. ((%14 (%15 ((%16 $0) $1))) (($4
       ((%115 $0) $2)) ((%115 $0) ((%18 ((%19 $1) $3)) $2))))))))))))) (%7
       (\%8. (%9 (\%10. (%11 (\%13. (%11 (\%12. ((%14 ((%16 $0) $1)) (($4
       ((%115 $0) $2)) ((%115 $0) ((%18 ((%19 $1) $3)) $2)))))))))))))))))
       (\%116. (\%117. ((%118 (\%12. (\%119. (((%24 (%25 %26)) (\%27.
       (\%10. ((%28 (\%13. (\%8. (%25 (((%29 ((%16 $5) $1)) ((%30 ((%31 $1)
       ((%32 %33) $0))) ($7 ((%115 $5) $2)))) ($7 ((%115 $5) $2)))))))
       $1)))) $0)))) $0)))))`)
  val initProds2Items_curried_def =
    DT([], [],
       `(%11 (\%120. (%9 (\%121. ((%36 ((%122 $1) $0)) (%110 ((%115 $1)
       $0)))))))`)
  val initItems_def =
    DT([], [],
       `(%47 (\%48. (%9 (\%123. ((%36 ((%124 $1) $0)) ((%86 $1) ((%122
       (%106 $1)) $0)))))))`)
  val moveDot_tupled_primitive_def =
    DT([], [],
       `((%125 %126) ((%127 (%128 (\%129. ((%5 (%130 $0)) ((%5 (%7 (\%131.
       (%7 (\%132. (%11 (\%133. (%45 (\%134. (%135 (\%136. (%135 (\%137.
       ((%14 ((%138 $0) $1)) (($6 ((%139 $2) $1)) ((%139 ((%30 ((%31 $3)
       ((%32 $4) ((%52 $0) $5)))) $2)) $1)))))))))))))))) ((%5 (%7 (\%131.
       (%7 (\%132. (%11 (\%133. (%45 (\%134. (%135 (\%136. (%135 (\%137.
       ((%14 (%15 ((%138 $0) $1))) (($6 ((%139 $2) $1)) ((%139 ((%30 ((%31
       $3) ((%32 $4) ((%52 $0) $5)))) $2)) $1)))))))))))))))) (%7 (\%140.
       (%11 (\%141. (%135 (\%136. (%45 (\%134. (($4 ((%139 $0) $1)) ((%139
       ((%30 ((%31 $2) ((%32 $3) %33))) $0)) $1)))))))))))))))) (\%142.
       (\%143. ((%144 (\%145. (\%136. (((%60 (%25 %26)) (\%61. (\%134.
       ((%62 (\%133. (\%146. ((%64 (\%132. (\%147. (((%66 (%25 ($9 ((%139
       $4) $6)))) (\%137. (\%131. (%25 (((%29 ((%138 $1) $8)) ((%30 ((%31
       $5) ((%32 ((%148 $3) ((%52 $1) %33))) $0))) ($11 ((%139 $6) $8))))
       ($11 ((%139 $6) $8))))))) $0)))) $0)))) $1)))) $1)))) $0)))))`)
  val moveDot_curried_def =
    DT([], [],
       `(%45 (\%149. (%135 (\%150. ((%36 ((%151 $1) $0)) (%126 ((%139 $1)
       $0)))))))`)
  val nextState_def =
    DT([], [],
       `(%47 (\%48. (%45 (\%152. (%135 (\%136. ((%36 (((%153 $2) $1) $0))
       ((%86 $2) ((%151 $1) $0)))))))))`)
  val validItl_tupled_primitive_def =
    DT([], [],
       `((%154 %155) ((%156 (%41 (\%42. ((%5 (%43 $0)) (%45 (\%157. (%47
       (\%48. (%7 (\%158. (%7 (\%159. (%11 (\%13. ((%14 ((%160 ((%19 $0)
       ((%148 $1) $2))) (%70 $3))) (($5 ((%49 $3) $4)) ((%49 $3) ((%30
       ((%31 $0) ((%32 $1) $2))) $4)))))))))))))))))) (\%161. (\%57. ((%162
       (\%48. (\%59. (((%163 (%164 %165)) (\%61. (\%157. ((%166 (\%13.
       (\%63. ((%167 (\%159. (\%158. (%164 ((%5 ((%160 ((%19 $3) ((%148 $1)
       $0))) (%70 $7))) ($9 ((%49 $7) $4))))))) $0)))) $1)))) $0))))
       $0)))))`)
  val validItl_curried_def =
    DT([], [],
       `(%47 (\%71. (%45 (\%72. ((%168 ((%169 $1) $0)) (%155 ((%49 $1)
       $0)))))))`)
  val validStates_tupled_primitive_def =
    DT([], [],
       `((%170 %171) ((%172 (%173 (\%174. ((%5 (%175 $0)) (%135 (\%136.
       (%176 (\%177. (%45 (\%152. (%47 (\%48. ((%14 ((%169 $0) $1)) (($4
       ((%178 $0) $2)) ((%178 $0) ((%179 ((%180 $3) $1)) $2))))))))))))))))
       (\%181. (\%182. ((%183 (\%48. (\%184. (((%185 (%164 %165)) (\%186.
       (\%177. ((%187 (\%136. (\%152. (%164 ((%5 ((%169 $5) $0)) ($7 ((%178
       $5) $2))))))) $1)))) $0)))) $0)))))`)
  val validStates_curried_def =
    DT([], [],
       `(%47 (\%71. (%176 (\%188. ((%168 ((%189 $1) $0)) (%171 ((%178 $1)
       $0)))))))`)
  val sgoto_def =
    DT([], [],
       `(%47 (\%48. (%45 (\%152. (%135 (\%136. ((%36 (((%190 $2) $1) $0))
       (((%153 $2) $1) $0))))))))`)
  val reduce_tupled_primitive_def =
    DT([], [],
       `((%191 %192) ((%193 (%194 (\%195. ((%5 (%196 $0)) ((%5 (%7 (\%8.
       (%45 (\%134. (%11 (\%13. (%47 (\%48. (%11 (\%12. ((%14 ((%101 (%53
       $0)) ((%197 $1) (%55 $2)))) (($5 ((%198 $1) ((%199 $3) $0))) ((%198
       $1) ((%199 ((%30 ((%31 $2) ((%32 $4) %33))) $3)) $0)))))))))))))))
       ((%5 (%7 (\%8. (%45 (\%134. (%11 (\%13. (%47 (\%48. (%11 (\%12.
       ((%14 (%15 ((%101 (%53 $0)) ((%197 $1) (%55 $2))))) (($5 ((%198 $1)
       ((%199 $3) $0))) ((%198 $1) ((%199 ((%30 ((%31 $2) ((%32 $4) %33)))
       $3)) $0))))))))))))))) (%7 (\%147. (%135 (\%200. (%7 (\%8. (%11
       (\%13. (%11 (\%12. (%45 (\%134. (%47 (\%48. (($7 ((%198 $0) ((%199
       $1) $2))) ((%198 $0) ((%199 ((%30 ((%31 $3) ((%32 $4) ((%52 $5)
       $6)))) $1)) $2))))))))))))))))))))))) (\%201. (\%202. ((%203 (\%48.
       (\%204. ((%205 (\%206. (\%12. (((%207 (%208 %107)) (\%83. (\%134.
       ((%209 (\%13. (\%146. ((%210 (\%8. (\%211. (((%212 (%208 (((%213
       ((%101 (%53 $6)) ((%197 $9) (%55 $3)))) ((%18 ((%19 $3) $1)) ($11
       ((%198 $9) ((%199 $4) $6))))) ($11 ((%198 $9) ((%199 $4) $6))))))
       (\%214. (\%215. (%208 ($13 ((%198 $11) ((%199 $6) $8))))))) $0))))
       $0)))) $1)))) $1)))) $0)))) $0)))))`)
  val reduce_curried_def =
    DT([], [],
       `(%47 (\%71. (%45 (\%72. (%11 (\%216. ((%217 (((%218 $2) $1) $0))
       (%192 ((%198 $2) ((%199 $1) $0))))))))))`)
  val buildTree_def =
    DT([], [],
       `(%219 (\%220. (%7 (\%8. ((%221 ((%222 $1) $0)) ((%223 (\%224.
       (((%225 ((%226 $0) %227)) %228) (((%225 ((%229 $1) (%230 $0)))
       ((%231 (%232 $1)) ((%233 %234) $2))) %228)))) ((%235 (%232 $0))
       ((%236 ((%237 %238) %234)) $1))))))))`)
  val addRule_def =
    DT(["DISK_THM"], [],
       `(%219 (\%220. (%11 (\%13. (%7 (\%8. ((%239 ((%240 $2) ((%19 $1)
       $0))) ((%241 (\%242. (((%243 ((%221 $0) %228)) %244) (%245 ((%246
       (%247 $2)) (%248 (%249 $0))))))) ((%222 $2) (%250 $0))))))))))`)
  val machine_def =
    DT([], [],
       `(%47 (\%48. ((%251 (%252 $0)) ((%253 (%190 $0)) (%218 $0)))))`)
  val slr_def =
    DT([], [],
       `(%47 (\%48. ((%254 (%255 $0)) ((%256 ((%257 (\%258. (\%259. (((%260
       (%261 (\%152. (%262 (\%136. ((%263 ((%264 (\%265. (\%123. ((%266
       (\%206. (\%267. (((%163 (((%268 %269) (\%270. (\%271. (((%268 %269)
       (\%272. (\%273. %165))) $0)))) $0)) (\%274. (\%275. (((%268 %269)
       (\%276. (\%277. (((%268 %165) (\%278. (\%279. %165))) $0)))) $2))))
       $1)))) ((%280 $1) $0))))) (($3 $1) $0))) (($2 $1) (%281 $0))))))))
       %282) (%283 ((%253 $1) $0)))))) (%190 $0))) (%218 $0)))))`)
  val ruleItems_defn_primitive_def =
    DT([], [],
       `((%284 %285) ((%286 (%287 (\%288. ((%5 (%289 $0)) ((%5 (%7 (\%290.
       (%135 (\%291. (%11 (\%13. (($3 ((%31 $0) ((%32 ((%52 $1) %33)) $2)))
       ((%31 $0) ((%32 %33) ((%52 $1) $2))))))))))) (%7 (\%290. (%135
       (\%291. (%7 (\%65. (%135 (\%292. (%11 (\%13. (($5 ((%31 $0) ((%32
       ((%148 ((%52 $1) $2)) ((%52 $3) %33))) $4))) ((%31 $0) ((%32 ((%52
       $1) $2)) ((%52 $3) $4))))))))))))))))))) (\%293. (\%294. ((%62
       (\%13. (\%295. ((%64 (\%296. (\%297. (((%66 (((%66 (%25 ((%30 ((%31
       $3) ((%32 %33) %33))) %26))) (\%291. (\%290. (%25 ((%30 ((%31 $5)
       ((%32 %33) ((%52 $1) $0)))) ($7 ((%31 $5) ((%32 ((%52 $1) %33))
       $0)))))))) $0)) (\%67. (\%211. (((%66 (%25 ((%30 ((%31 $5) ((%32
       ((%52 $1) $0)) %33))) %26))) (\%214. (\%215. (%25 ((%30 ((%31 $7)
       ((%32 ((%52 $3) $2)) ((%52 $1) $0)))) ($9 ((%31 $7) ((%32 ((%148
       ((%52 $3) $2)) ((%52 $1) %33))) $0)))))))) $2)))) $1)))) $0))))
       $0)))))`)
  val itemPair_def =
    DT(["DISK_THM"], [],
       `(%11 (\%13. (%298 (\%299. ((%300 (%301 ((%31 $1) $0))) $0)))))`)
  val allItems_primitive_def =
    DT([], [],
       `((%87 %302) ((%89 (%90 (\%91. ((%5 (%92 $0)) (%7 (\%8. (%11 (\%13.
       (%9 (\%10. (($3 $0) ((%18 ((%19 $1) $2)) $0)))))))))))) (\%303.
       (\%95. (((%24 (%25 %26)) (\%96. (\%10. ((%28 (\%13. (\%8. (%25 ((%69
       (%285 ((%31 $1) ((%32 %33) $0)))) ($5 $2)))))) $1)))) $0)))))`)
  val symNeighbour_def =
    DT([], [],
       `(%47 (\%48. (%45 (\%152. (%135 (\%136. ((%36 (((%304 $2) $1) $0))
       (%79 ((%86 $2) ((%151 $1) $0))))))))))`)
  val asNeighbours_def =
    DT(["DISK_THM"], [],
       `((%5 (%47 (\%48. (%45 (\%152. ((%305 (((%306 $1) $0) %33))
       %307)))))) (%47 (\%48. (%45 (\%152. (%135 (\%291. (%7 (\%290. ((%305
       (((%306 $3) $2) ((%52 $1) $0))) ((%308 (((%304 $3) $2) $1)) (((%306
       $3) $2) $0))))))))))))`)
  val visit_defn_tupled_primitive_def =
    DT([], [],
       `((%309 %310) ((%311 (%312 (\%313. ((%5 (%314 $0)) (%315 (\%316.
       (%47 (\%48. (%45 (\%152. (%315 (\%317. (%315 (\%318. (%45 (\%319.
       ((%14 ((%5 (%15 ((%320 (%15 (%321 $3))) (%15 ((%169 $4) $3))))) ((%5
       ((%305 $2) (((%306 $4) $3) (%322 (%323 $4))))) ((%5 ((%305 $1)
       ((%324 $2) $5))) ((%325 $0) $1))))) (($6 ((%326 $4) ((%327 ((%328
       $5) $1)) $0))) ((%326 $4) ((%327 $5) $3)))))))))))))))))))) (\%329.
       (\%330. ((%331 (\%48. (\%332. ((%333 (\%316. (\%152. (%334 (((%335
       ((%320 (%15 (%321 $0))) (%15 ((%169 $3) $0)))) %307) ((%336 (\%317.
       ((%336 (\%318. ((%328 $0) (%337 ((%338 (\%319. ($8 ((%326 $6) ((%327
       ((%328 $4) $1)) $0))))) $0))))) ((%324 $0) $2)))) (((%306 $3) $0)
       (%322 (%323 $3))))))))) $0)))) $0)))))`)
  val visit_defn_curried_def =
    DT([], [],
       `(%47 (\%71. (%315 (\%339. (%45 (\%340. ((%305 (((%341 $2) $1) $0))
       (%310 ((%326 $2) ((%327 $1) $0))))))))))`)
  val validItem_tupled_primitive_def =
    DT([], [],
       `((%342 %343) ((%344 (%345 (\%346. (%347 $0)))) (\%348. (\%349.
       ((%350 (\%48. (\%351. ((%166 (\%13. (\%352. ((%167 (\%159. (\%158.
       (%164 ((%160 ((%19 $3) ((%148 $1) $0))) (%70 $5)))))) $0)))) $0))))
       $0)))))`)
  val validItem_curried_def =
    DT([], [],
       `(%47 (\%71. (%76 (\%353. ((%168 ((%354 $1) $0)) (%343 ((%355 $1)
       $0)))))))`)
  val isGrammarItl_def =
    DT([], [],
       `(%47 (\%48. (%45 (\%152. ((%168 ((%356 $1) $0)) ((%357 (%354 $1))
       $0))))))`)
  val allGrammarItls_def =
    DT([], [],
       `(%47 (\%48. ((%358 (%359 $0)) (%360 (\%152. ((%361 $0) ((%5 ((%356
       $1) $0)) (%321 $0))))))))`)
  val itemLhs_def =
    DT(["DISK_THM"], [],
       `(%11 (\%13. (%298 (\%362. ((%16 (%363 ((%31 $1) $0))) $1)))))`)
  val itemFstRhs_def =
    DT(["DISK_THM"], [],
       `(%11 (\%13. (%298 (\%362. ((%229 (%364 ((%31 $1) $0))) (%365
       $0))))))`)
  val itemSndRhs_def =
    DT(["DISK_THM"], [],
       `(%11 (\%13. (%298 (\%362. ((%229 (%366 ((%31 $1) $0))) (%367
       $0))))))`)
  val slrML4Sym_def =
    DT(["DISK_THM"], [],
       `((%5 (%47 (\%48. (%135 (\%136. ((%254 (((%368 $1) %307) $0)) (%283
       ((%253 (%190 $1)) (%218 $1))))))))) (%47 (\%48. (%45 (\%369. (%315
       (\%370. (%135 (\%136. ((%254 (((%368 $3) ((%308 $2) $1)) $0)) ((%371
       (\%265. ((%372 (\%123. ((%373 (\%145. (\%119. (((%374 (((%375
       (((%368 $7) $5) $4)) (\%270. (\%376. (((%375 (((%368 $9) $7) $6))
       (\%272. (\%273. %282))) $0)))) $0)) (\%274. (\%275. (((%375 (((%368
       $9) $7) $6)) (\%276. (\%377. (((%375 %282) (\%278. (\%279. %282)))
       $0)))) $2)))) $1)))) ((%280 $1) $0)))) (((%218 $4) $3) (%281 $1)))))
       (((%190 $3) $2) $0))))))))))))`)
  val slrML_def =
    DT(["DISK_THM"], [],
       `((%5 (%47 (\%48. (%315 (\%370. ((%254 (((%378 $1) $0) %33)) (%283
       ((%253 (%190 $1)) (%218 $1))))))))) (%47 (\%48. (%315 (\%370. (%135
       (\%136. (%7 (\%379. ((%254 (((%378 $3) $2) ((%52 $1) $0))) (((%260
       ((%254 (((%368 $3) $2) $1)) %282)) %282) (((%378 $3) $2)
       $0))))))))))))`)
  val findItemInRules_tupled_primitive_def =
    DT([], [],
       `((%380 %381) ((%382 (%383 (\%384. (%385 $0)))) (\%386. (\%387.
       ((%388 (\%389. (\%267. ((%166 (\%390. (\%146. ((%167 (\%159. (\%147.
       (((%391 (((%268 (%164 %269)) (\%392. (\%93. ((%393 (\%394. (\%158.
       (%164 %165)))) $1)))) $4)) (\%395. (\%396. (%164 %269)))) $0))))
       $0)))) $1)))) $0)))))`)
  val findItemInRules_curried_def =
    DT([], [],
       `(%76 (\%397. (%9 (\%121. ((%168 ((%398 $1) $0)) (%381 ((%399 $1)
       $0)))))))`)
  val itemEqRuleList_defn_tupled_primitive_def =
    DT([], [],
       `((%400 %401) ((%402 (%403 (\%404. ((%5 (%405 $0)) (%9 (\%406. (%407
       (\%408. (%45 (\%409. (%76 (\%410. ((%14 ((%5 (%15 (%15 ((%411 (%412
       ((%30 $0) $1))) (%413 ((%18 $2) $3)))))) ((%398 (%414 ((%30 $0)
       $1))) ((%18 $2) $3)))) (($4 ((%280 (%415 ((%30 $0) $1))) ((%18 $2)
       $3))) ((%280 ((%30 $0) $1)) ((%18 $2) $3)))))))))))))))) (\%416.
       (\%417. ((%266 (\%145. (\%418. (((%163 (((%268 (%164 %165)) (\%419.
       (\%420. (%164 %165)))) $0)) (\%421. (\%422. (((%268 (%164 %269))
       (\%423. (\%424. (%164 (((%425 (%15 ((%411 (%412 ((%30 $3) $2)))
       (%413 ((%18 $1) $0))))) %269) (((%425 ((%398 (%414 ((%30 $3) $2)))
       ((%18 $1) $0))) ($7 ((%280 (%415 ((%30 $3) $2))) ((%18 $1) $0))))
       %269)))))) $2)))) $1)))) $0)))))`)
  val itemEqRuleList_defn_curried_def =
    DT([], [],
       `(%45 (\%149. (%9 (\%121. ((%168 ((%426 $1) $0)) (%401 ((%280 $1)
       $0)))))))`)
  val getState_def =
    DT(["DISK_THM"], [],
       `(%427 (\%258. (%428 (\%259. (%45 (\%152. (%135 (\%136. ((%429
       (((%430 ((%253 $3) $2)) $1) $0)) ((%431 ((%432 (\%433. (\%434.
       ((%435 (\%145. (\%119. (((%436 (((%437 %438) (\%439. (\%440. (((%441
       ((%411 (%413 $4)) (%442 (%443 %444)))) (%445 (%446 $4))) %438))))
       $0)) (\%397. (\%447. (((%437 (%448 ((%180 $6) $5))) (\%449. (\%450.
       (((%441 ((%426 ((%30 $3) $2)) ((%18 $1) $0))) (%445 (%446 $6)))
       %438)))) $2)))) $1)))) ((%280 $1) $0))))) (($3 $1) $0))) (($2 $1)
       (%281 $0))))))))))))`)
  val doReduce_tupled_primitive_def =
    DT([], [],
       `((%451 %452) ((%453 (%454 (\%455. (%456 $0)))) (\%457. (\%458.
       ((%459 (\%460. (\%461. ((%462 (\%463. (\%464. ((%465 (\%466. (\%467.
       (((%468 %469) (\%136. (\%379. ((%470 (\%471. (\%472. (((%473 %469)
       (\%474. (\%475. ((%476 (\%137. (\%152. (%477 (((%478 (%479 $7))
       %480) ((%481 ((%482 (\%13. (\%8. ((%483 (\%484. (((%485 %480)
       (\%486. ((%487 (\%488. ((%489 (\%490. (((%478 ((%491 $0) %492))
       %480) ((%493 (\%494. ((%495 (\%496. (%497 ((%498 ((%52 $15) $14))
       ((%499 ((%500 ((%501 ((%502 $0) $4)) %503)) $3)) ((%504 $2) $0))))))
       ((%180 (%55 $6)) (((%505 $20) $0) (%55 $6)))))) (%506 (%507 $0))))))
       ((%508 ((%179 ((%180 $6) $5)) $7)) (%232 $3))))) ((%509 $9) (%232
       $2))))) $0))) ((%510 $7) $12))))) (%511 $10))) (%512 $10)))))))
       $1)))) $0)))) $2)))) $1)))) $1)))) $0)))) $0)))))`)
  val doReduce_curried_def =
    DT([], [],
       `(%513 (\%514. (%515 (\%516. (%407 (\%517. ((%518 (((%519 $2) $1)
       $0)) (%452 ((%520 $2) ((%521 $1) $0))))))))))`)
  val parse_tupled_primitive_def =
    DT([], [],
       `((%522 %523) ((%524 (%525 (\%526. (%527 $0)))) (\%528. (\%529.
       ((%530 (\%531. (\%532. ((%465 (\%533. (\%534. ((%470 (\%471. (\%535.
       (((%473 %469) (\%536. (\%475. ((%476 (\%137. (\%152. (%477 (((%537
       %480) (\%538. (((%468 %480) (\%539. (\%540. (((%468 ((%541 (\%542.
       ((((%543 (\%464. (((%544 $4) ((%498 ((%52 $3) %33)) ((%499 $10)
       ((%179 ((%180 $6) $5)) $7)))) $0))) (\%545. %480)) %480) $0)))
       (((%430 $2) $3) $1))) (\%546. (\%547. ((%541 (\%542. ((((%543
       (\%464. (((%544 $6) ((%498 ((%52 $5) ((%52 $3) $2))) ((%499 $12)
       ((%179 ((%180 $8) $7)) $9)))) $0))) (\%545. (((%478 (%479 $5)) %480)
       (%497 ((%498 ((%52 $3) $2)) ((%499 ((%501 ((%502 $0) (%548 (%549
       (%550 $5))))) $12)) ((%504 ((%179 ((%180 $8) $7)) $9)) $0)))))))
       %480) $0))) (((%430 $4) $5) $3))))) $0)))) $8))) $9))))) $1))))
       $0)))) $0)))) $0)))) $0)))))`)
  val parse_curried_def =
    DT([], [],
       `(%551 (\%552. (%515 (\%516. ((%518 ((%553 $1) $0)) (%523 ((%554 $1)
       $0)))))))`)
  val parser_def =
    DT([], [],
       `(%47 (\%48. (%551 (\%555. (%7 (\%556. (%557 (\%558. (%176 (\%559.
       (%135 (\%560. (%135 (\%561. ((%562 (((((((%563 $6) $5) $4) $3) $2)
       $1) $0)) ((%564 (\%565. (((%566 %567) (\%568. (((%569 (%570 %244))
       (\%463. ((%571 (\%572. (\%573. ((%574 (\%575. (\%576. (((%577 (%570
       %244)) (\%578. (\%579. ((%580 (\%581. (\%582. (((%577 (%570 (%245
       ((%246 (%247 (%106 $17))) ((%583 ((%584 $0) %585)) ((%584 (%548
       (%549 (%550 $12)))) %585)))))) (\%586. (\%587. (%570 %244)))) $2))))
       $1)))) $1)))) $0)))) $0))) $0))) $0))) (((%588 (%589 (\%590. (%591
       (\%592. (\%593. ((%320 (%15 ((%229 $2) ((%52 $4) %33)))) (%15 ((%138
       (%594 (%595 (%596 $1)))) $3))))))))) (%597 (\%590. (%598 (\%592.
       (\%593. ((%553 $8) ((%498 $2) ((%499 $1) $0))))))))) (%497 ((%498
       $4) ((%499 $3) $2))))))))))))))))))))`)
  val yacc_def =
    DT([], [],
       `(%47 (\%48. (%11 (\%599. (%11 (\%97. (%7 (\%556. ((%239 ((((%600
       $3) $2) $1) $0)) ((%601 (\%602. (((%603 %244) (\%604. ((%605 (\%531.
       (((%606 %244) (\%538. ((%607 (\%608. (((%609 %244) (\%610. (((%611
       %244) (\%612. (%245 $0))) $0))) (((((((%563 $3) (%283 $1)) $5) %503)
       ((%179 $0) %492)) (%53 $6)) (%55 (%106 $8)))))) ((%180 (%55 $6))
       ((%124 $2) (%70 $2)))))) $0))) (%255 $0)))) $0))) (((%99 $3) $2)
       $1)))))))))))`)
  val getItems_ind =
    DT(["DISK_THM"], [],
       `(%613 (\%614. ((%14 ((%5 (%11 (\%12. (($1 %107) $0)))) (%11 (\%13.
       (%7 (\%8. (%9 (\%10. (%11 (\%12. ((%14 ((%5 ((%14 (%15 ((%16 $3)
       $0))) (($4 $1) $0))) ((%14 ((%16 $3) $0)) (($4 $1) $0)))) (($4 ((%18
       ((%19 $3) $2)) $1)) $0)))))))))))) (%9 (\%23. (%11 (\%615. (($2 $1)
       $0))))))))`)
  val getItems_def =
    DT(["DISK_THM"], [],
       `((%5 ((%36 ((%37 %107) %12)) %26)) ((%36 ((%37 ((%18 ((%19 %13)
       %8)) %10)) %12)) (((%29 ((%16 %13) %12)) ((%30 ((%31 %13) ((%32 %33)
       %8))) ((%37 %10) %12))) ((%37 %10) %12))))`)
  val iclosure1_ind =
    DT(["DISK_THM"], [],
       `(%616 (\%617. ((%14 ((%5 (%47 (\%48. (($1 $0) %26)))) ((%5 (%47
       (\%48. (%11 (\%12. (%7 (\%44. (%45 (\%46. ((%14 (($4 $3) $0)) (($4
       $3) ((%30 ((%31 $2) ((%32 $1) %33))) $0)))))))))))) ((%5 (%47 (\%48.
       (%11 (\%12. (%7 (\%44. (%11 (\%51. (%7 (\%50. (%45 (\%46. ((%14 (($6
       $5) $0)) (($6 $5) ((%30 ((%31 $4) ((%32 $3) ((%52 (%53 $2)) $1))))
       $0)))))))))))))))) (%47 (\%48. (%11 (\%12. (%7 (\%44. (%11 (\%54.
       (%7 (\%50. (%45 (\%46. ((%14 (($6 $5) $0)) (($6 $5) ((%30 ((%31 $4)
       ((%32 $3) ((%52 (%55 $2)) $1)))) $0))))))))))))))))))) (%47 (\%618.
       (%45 (\%59. (($2 $1) $0))))))))`)
  val iclosure1_def =
    DT(["DISK_THM"], [],
       `((%5 ((%36 ((%73 %48) %26)) %26)) ((%5 ((%36 ((%73 %48) ((%30 ((%31
       %12) ((%32 %44) %33))) %46))) ((%30 ((%31 %12) ((%32 %44) %33)))
       ((%73 %48) %46)))) ((%5 ((%36 ((%73 %48) ((%30 ((%31 %12) ((%32 %44)
       ((%52 (%53 %51)) %50)))) %46))) ((%30 ((%31 %12) ((%32 %44) ((%52
       (%53 %51)) %50)))) ((%73 %48) %46)))) ((%36 ((%73 %48) ((%30 ((%31
       %12) ((%32 %44) ((%52 (%55 %54)) %50)))) %46))) ((%69 ((%69 ((%37
       (%70 %48)) %54)) ((%30 ((%31 %12) ((%32 %44) ((%52 (%55 %54))
       %50)))) %26))) ((%73 %48) %46))))))`)
  val rules2Items_ind =
    DT(["DISK_THM"], [],
       `(%619 (\%620. ((%14 ((%5 ($0 %107)) (%11 (\%13. (%7 (\%8. (%9
       (\%93. ((%14 ($3 $0)) ($3 ((%18 ((%19 $2) $1)) $0))))))))))) (%9
       (\%23. ($1 $0))))))`)
  val rules2Items_def =
    DT(["DISK_THM"], [],
       `((%5 ((%36 (%88 %107)) %26)) ((%36 (%88 ((%18 ((%19 %13) %8))
       %93))) ((%30 ((%31 %13) ((%32 %33) %8))) (%88 %93))))`)
  val iclosure1_mem =
    DT(["DISK_THM"], [],
       `(%76 (\%621. (%45 (\%622. ((%14 ((%623 $1) $0)) ((%623 $1) ((%73
       %48) $0)))))))`)
  val iclosure1_not_nil =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%76 (\%397. (%45 (\%447. (%15 ((%36 ((%73 $2) ((%30
       $1) $0))) %26))))))))`)
  val iclosure1_len =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%622. ((%624 (%412 ((%73 $1) $0))) (%412 (%79
       $0)))))))`)
  val rules2items_sub =
    DT(["DISK_THM"], [],
       `(%76 (\%621. (%11 (\%625. (%9 (\%10. ((%14 ((%623 $2) ((%37 $0)
       $1))) ((%623 $2) (%88 $0)))))))))`)
  val iclosure1_outmem =
    DT(["DISK_THM"], [],
       `(%76 (\%621. (%45 (\%622. ((%14 ((%623 $1) ((%73 %48) $0))) ((%14
       (%15 ((%623 $1) $0))) ((%623 $1) (%88 (%70 %48)))))))))`)
  val iclosure1_before_after_len =
    DT(["DISK_THM"], [],
       `(%45 (\%622. ((%14 ((%626 (%627 (%81 ((%73 %48) $0)))) (%627 (%81
       $0)))) ((%626 ((%628 (%627 ((%629 (%81 (%88 (%70 %48)))) (%81 ((%73
       %48) $0))))) (%627 ((%629 (%81 (%88 (%70 %48)))) (%81 $0)))))
       %630))))`)
  val iclosure =
    DT(["DISK_THM"], [],
       `((%5 ((%36 ((%86 %48) %26)) %26)) ((%36 ((%86 %48) ((%30 %61)
       %75))) ((%85 (\%77. ((%85 (\%78. (((%29 (%15 ((%80 (%81 $1)) (%81
       $0)))) ((%86 %48) $0)) $0))) (%79 ((%73 %48) $0))))) (%79 ((%30 %61)
       %75)))))`)
  val iclosure_ind =
    DT(["DISK_THM"], [],
       `(%616 (\%617. ((%14 ((%5 (%47 (\%48. (($1 $0) %26)))) (%47 (\%48.
       (%76 (\%61. (%45 (\%75. ((%14 (%45 (\%77. (%45 (\%78. ((%14 ((%5
       ((%36 $1) (%79 ((%30 $3) $2)))) ((%5 ((%36 $0) (%79 ((%73 $4) $1))))
       (%15 ((%80 (%81 $1)) (%81 $0)))))) (($5 $4) $0))))))) (($3 $2) ((%30
       $1) $0))))))))))) (%47 (\%618. (%45 (\%59. (($2 $1) $0))))))))`)
  val iclosure_nil =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%622. ((%14 (%15 ((%36 $0) %26))) (%15 ((%36
       ((%86 $1) $0)) %26)))))))`)
  val ag_new_rule =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%11 (\%12. (%11 (\%97. ((%14 ((%98 (((%99 $2) $1) $0))
       (%103 %604))) ((%5 ((%160 ((%19 $1) ((%52 (%55 (%106 $2))) ((%52
       (%53 $0)) %33)))) (%70 %604))) ((%16 $1) (%106 %604))))))))))`)
  val initProds2Items_ind =
    DT(["DISK_THM"], [],
       `(%631 (\%632. ((%14 ((%5 (%11 (\%12. (($1 $0) %107)))) (%11 (\%12.
       (%11 (\%13. (%7 (\%8. (%9 (\%10. ((%14 ((%5 ((%14 (%15 ((%16 $3)
       $2))) (($4 $3) $0))) ((%14 ((%16 $3) $2)) (($4 $3) $0)))) (($4 $3)
       ((%18 ((%19 $2) $1)) $0))))))))))))) (%11 (\%633. (%9 (\%119. (($2
       $1) $0))))))))`)
  val initProds2Items_def =
    DT(["DISK_THM"], [],
       `((%5 ((%36 ((%122 %12) %107)) %26)) ((%36 ((%122 %12) ((%18 ((%19
       %13) %8)) %10))) (((%29 ((%16 %12) %13)) ((%30 ((%31 %13) ((%32 %33)
       %8))) ((%122 %12) %10))) ((%122 %12) %10))))`)
  val moveDot_ind =
    DT(["DISK_THM"], [],
       `(%634 (\%635. ((%14 ((%5 (%135 (\%136. (($1 %26) $0)))) ((%5 (%11
       (\%133. (%7 (\%132. (%135 (\%137. (%7 (\%131. (%45 (\%134. (%135
       (\%136. ((%14 ((%5 ((%14 (%15 ((%138 $3) $0))) (($6 $1) $0))) ((%14
       ((%138 $3) $0)) (($6 $1) $0)))) (($6 ((%30 ((%31 $5) ((%32 $4) ((%52
       $3) $2)))) $1)) $0))))))))))))))) (%11 (\%141. (%7 (\%140. (%45
       (\%134. (%135 (\%136. ((%14 (($4 $1) $0)) (($4 ((%30 ((%31 $3) ((%32
       $2) %33))) $1)) $0))))))))))))) (%45 (\%145. (%135 (\%636. (($2 $1)
       $0))))))))`)
  val moveDot_def =
    DT(["DISK_THM"], [],
       `((%5 ((%36 ((%151 %26) %136)) %26)) ((%5 ((%36 ((%151 ((%30 ((%31
       %133) ((%32 %132) ((%52 %137) %131)))) %134)) %136)) (((%29 ((%138
       %137) %136)) ((%30 ((%31 %133) ((%32 ((%148 %132) ((%52 %137) %33)))
       %131))) ((%151 %134) %136))) ((%151 %134) %136)))) ((%36 ((%151
       ((%30 ((%31 %141) ((%32 %140) %33))) %134)) %136)) ((%151 %134)
       %136))))`)
  val validItl_ind =
    DT(["DISK_THM"], [],
       `(%616 (\%617. ((%14 ((%5 (%47 (\%48. (($1 $0) %26)))) (%47 (\%48.
       (%11 (\%13. (%7 (\%159. (%7 (\%158. (%45 (\%157. ((%14 ((%14 ((%160
       ((%19 $3) ((%148 $2) $1))) (%70 $4))) (($5 $4) $0))) (($5 $4) ((%30
       ((%31 $3) ((%32 $2) $1))) $0))))))))))))))) (%47 (\%618. (%45 (\%59.
       (($2 $1) $0))))))))`)
  val validItl_def =
    DT(["DISK_THM"], [],
       `((%5 ((%168 ((%169 %48) %26)) %165)) ((%168 ((%169 %48) ((%30 ((%31
       %13) ((%32 %159) %158))) %157))) ((%5 ((%160 ((%19 %13) ((%148 %159)
       %158))) (%70 %48))) ((%169 %48) %157))))`)
  val validStates_ind =
    DT(["DISK_THM"], [],
       `(%637 (\%638. ((%14 ((%5 (%47 (\%48. (($1 $0) %492)))) (%47 (\%48.
       (%135 (\%136. (%45 (\%152. (%176 (\%177. ((%14 ((%14 ((%169 $3) $1))
       (($4 $3) $0))) (($4 $3) ((%179 ((%180 $2) $1)) $0))))))))))))) (%47
       (\%618. (%176 (\%184. (($2 $1) $0))))))))`)
  val validStates_def =
    DT(["DISK_THM"], [],
       `((%5 ((%168 ((%189 %48) %492)) %165)) ((%168 ((%189 %48) ((%179
       ((%180 %136) %152)) %177))) ((%5 ((%169 %48) %152)) ((%189 %48)
       %177))))`)
  val validItl_append =
    DT(["DISK_THM"], [],
       `((%168 ((%169 %48) ((%69 %639) %640))) ((%5 ((%169 %48) %639))
       ((%169 %48) %640)))`)
  val validStates_append =
    DT(["DISK_THM"], [],
       `(%176 (\%641. (%176 (\%642. ((%168 ((%189 %48) ((%643 $1) $0)))
       ((%5 ((%189 %48) $1)) ((%189 %48) $0)))))))`)
  val validStates_pop =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%176 (\%644. (%645 (\%646. ((%14 ((%189 $2) $1))
       ((%189 $2) ((%508 $1) $0)))))))))`)
  val validItl_md =
    DT(["DISK_THM"], [],
       `(%45 (\%152. (%135 (\%136. ((%14 ((%169 %48) $1)) ((%169 %48)
       ((%151 $1) $0)))))))`)
  val validItl_rules_cons =
    DT(["DISK_THM"], [],
       `(%9 (\%123. (%11 (\%12. (%45 (\%622. (%407 (\%647. ((%14 ((%169
       ((%104 $3) $2)) $1)) ((%169 ((%104 ((%18 $0) $3)) $2))
       $1))))))))))`)
  val rules2items_sub2 =
    DT(["DISK_THM"], [], `(%47 (\%48. ((%169 $0) (%88 (%70 $0)))))`)
  val validItl_mem =
    DT(["DISK_THM"], [],
       `(%45 (\%622. ((%168 ((%169 %48) $0)) (%76 (\%621. ((%14 ((%623 $0)
       $1)) ((%169 %48) ((%30 $0) %26))))))))`)
  val validItl_getItems =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%11 (\%648. ((%169 $1) ((%37 (%70 $1)) $0))))))`)
  val validItl_iclosure1 =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%152. ((%14 ((%169 $1) $0)) ((%169 $1) ((%73 $1)
       $0)))))))`)
  val validItl_delete =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%649. (%76 (\%650. ((%14 ((%169 $2) $1)) ((%169
       $2) ((%651 $0) $1)))))))))`)
  val validItl_rmDupes =
    DT(["DISK_THM"], [],
       `(%45 (\%152. ((%14 ((%169 %48) $0)) ((%169 %48) (%79 $0)))))`)
  val validItl_iclosure =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%152. ((%14 ((%169 $1) $0)) ((%169 $1) ((%86 $1)
       $0)))))))`)
  val validItl_sgoto =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%152. (%135 (\%136. ((%14 ((%169 $2) $1)) ((%169
       $2) (((%190 $2) $1) $0)))))))))`)
  val reduce_ind =
    DT(["DISK_THM"], [],
       `(%652 (\%653. ((%14 ((%5 (%47 (\%48. (%11 (\%12. ((($2 $1) %26)
       $0)))))) ((%5 (%47 (\%48. (%11 (\%13. (%7 (\%8. (%45 (\%134. (%11
       (\%12. ((%14 ((%5 ((%14 (%15 ((%101 (%53 $0)) ((%197 $4) (%55
       $3))))) ((($5 $4) $1) $0))) ((%14 ((%101 (%53 $0)) ((%197 $4) (%55
       $3)))) ((($5 $4) $1) $0)))) ((($5 $4) ((%30 ((%31 $3) ((%32 $2)
       %33))) $1)) $0))))))))))))) (%47 (\%48. (%11 (\%13. (%7 (\%8. (%135
       (\%200. (%7 (\%147. (%45 (\%134. (%11 (\%12. ((%14 ((($7 $6) $1)
       $0)) ((($7 $6) ((%30 ((%31 $5) ((%32 $4) ((%52 $3) $2)))) $1))
       $0))))))))))))))))))) (%47 (\%618. (%45 (\%59. (%11 (\%654. ((($3
       $2) $1) $0))))))))))`)
  val reduce_def =
    DT(["DISK_THM"], [],
       `((%5 ((%217 (((%218 %48) %26) %12)) %107)) ((%5 ((%217 (((%218 %48)
       ((%30 ((%31 %13) ((%32 %8) %33))) %134)) %12)) (((%213 ((%101 (%53
       %12)) ((%197 %48) (%55 %13)))) ((%18 ((%19 %13) %8)) (((%218 %48)
       %134) %12))) (((%218 %48) %134) %12)))) ((%217 (((%218 %48) ((%30
       ((%31 %13) ((%32 %8) ((%52 %200) %147)))) %134)) %12)) (((%218 %48)
       %134) %12))))`)
  val allItems_ind =
    DT(["DISK_THM"], [],
       `(%619 (\%620. ((%14 ((%5 ($0 %107)) (%11 (\%13. (%7 (\%8. (%9
       (\%10. ((%14 ($3 $0)) ($3 ((%18 ((%19 $2) $1)) $0))))))))))) (%9
       (\%23. ($1 $0))))))`)
  val allItems_def =
    DT(["DISK_THM"], [],
       `((%5 ((%36 (%302 %107)) %26)) ((%36 (%302 ((%18 ((%19 %13) %8))
       %10))) ((%69 (%285 ((%31 %13) ((%32 %33) %8)))) (%302 %10))))`)
  val validItem_ind =
    DT(["DISK_THM"], [],
       `(%655 (\%656. ((%14 (%47 (\%48. (%11 (\%13. (%7 (\%159. (%7 (\%158.
       (($4 $3) ((%31 $2) ((%32 $1) $0)))))))))))) (%47 (\%618. (%76
       (\%351. (($2 $1) $0))))))))`)
  val validItem_def =
    DT(["DISK_THM"], [],
       `((%168 ((%354 %48) ((%31 %13) ((%32 %159) %158)))) ((%160 ((%19
       %13) ((%148 %159) %158))) (%70 %48)))`)
  val finite_allItems =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%657 (%658 (\%659. ((%660 $0) ((%623 $0) (%302 (%70
       $1)))))))))`)
  val validItemRulesEqGrRules =
    DT(["DISK_THM"], [],
       `(%47 (\%48. ((%661 (%662 (%663 (\%13. (%664 (\%159. (\%158. ((%665
       ((%19 $2) ((%148 $1) $0))) ((%354 $3) ((%31 $2) ((%32 $1)
       $0))))))))))) (%666 (%70 $0)))))`)
  val allItems_append =
    DT(["DISK_THM"], [],
       `(%9 (\%667. (%9 (\%668. ((%36 (%302 ((%105 $1) $0))) ((%69 (%302
       $1)) (%302 $0)))))))`)
  val ruleItems_mem =
    DT(["DISK_THM"], [],
       `(%76 (\%669. ((%623 ((%31 (%363 $0)) ((%32 ((%148 (%364 $0)) (%366
       $0))) %33))) (%285 $0))))`)
  val allMemRuleItems =
    DT(["DISK_THM"], [],
       `(%76 (\%669. (%7 (\%159. (%7 (\%158. ((%14 ((%229 (%366 $2)) ((%148
       $1) $0))) ((%623 ((%31 (%363 $2)) ((%32 ((%148 (%364 $2)) $1)) $0)))
       (%285 $2)))))))))`)
  val memRuleAllItems =
    DT(["DISK_THM"], [],
       `(%11 (\%13. (%7 (\%8. (%9 (\%10. ((%14 ((%160 ((%19 $2) $1)) $0))
       (%7 (\%159. (%7 (\%158. ((%14 ((%229 $3) ((%148 $1) $0))) ((%623
       ((%31 $4) ((%32 $1) $0))) (%302 $2))))))))))))))`)
  val itemEqRule =
    DT(["DISK_THM"], [],
       `(%76 (\%669. (%11 (\%12. (%7 (\%670. (%7 (\%8. ((%14 ((%623 ((%31
       $2) ((%32 $1) $0))) (%285 $3))) ((%5 ((%16 $2) (%363 $3))) ((%229
       ((%148 $1) $0)) ((%148 (%364 $3)) (%366 $3)))))))))))))`)
  val memAllItemsRules =
    DT(["DISK_THM"], [],
       `(%9 (\%10. (%11 (\%12. (%7 (\%670. (%7 (\%8. ((%14 ((%623 ((%31 $2)
       ((%32 $1) $0))) (%302 $3))) ((%160 ((%19 $2) ((%148 $1) $0)))
       $3))))))))))`)
  val validItemEqAllItems =
    DT(["DISK_THM"], [],
       `(%47 (\%48. ((%80 (%658 (\%397. ((%660 $0) ((%354 $1) $0))))) (%81
       (%302 (%70 $0))))))`)
  val finite_validItem = DT(["DISK_THM"], [], `(%657 (%354 %48))`)
  val finiteAllGrItls =
    DT(["DISK_THM"], [], `(%47 (\%48. (%671 (%359 $0))))`)
  val prop_mem =
    DT(["DISK_THM"], [],
       `(%672 (\%673. (%7 (\%674. ((%14 ((%325 %675) (((%306 %48) %152)
       $0))) (%262 (\%676. ((%5 ((%677 $0) $1)) ((%325 %675) (((%306 %48)
       %152) ((%52 $0) %33)))))))))))`)
  val validItl_evmem =
    DT(["DISK_THM"], [],
       `(%45 (\%622. ((%168 ((%169 %48) $0)) ((%357 (%354 %48)) $0))))`)
  val validItl_symNeighbour =
    DT(["DISK_THM"], [],
       `(%45 (\%152. ((%14 ((%169 %48) $0)) ((%357 (%354 %48)) (((%304 %48)
       $0) %136)))))`)
  val symNeighbour_allDistinct =
    DT(["DISK_THM"], [],
       `(%47 (\%48. (%45 (\%152. (%135 (\%136. (%321 (((%304 $2) $1)
       $0))))))))`)
  val ar1 =
    DT(["DISK_THM"], [],
       `(%645 (\%678. (%645 (\%679. (%645 (\%680. ((%14 ((%624 $2) $0))
       ((%168 ((%681 $2) ((%682 $1) ((%628 $2) $0)))) ((%681 %630) ((%628
       $1) $0))))))))))`)
  val findItemInRules_ind =
    DT(["DISK_THM"], [],
       `(%683 (\%684. ((%14 ((%5 (%11 (\%390. (%7 (\%159. (($2 ((%31 $1)
       ((%32 $0) %33))) %107)))))) ((%5 (%11 (\%390. (%7 (\%159. (%11
       (\%394. (%7 (\%158. (%9 (\%93. (($5 ((%31 $4) ((%32 $3) %33))) ((%18
       ((%19 $2) $1)) $0))))))))))))) (%11 (\%141. (%7 (\%140. (%135
       (\%214. (%7 (\%215. (%9 (\%418. (($5 ((%31 $4) ((%32 $3) ((%52 $2)
       $1)))) $0)))))))))))))) (%76 (\%389. (%9 (\%119. (($2 $1)
       $0))))))))`)
  val findItemInRules_def =
    DT(["DISK_THM"], [],
       `((%5 ((%168 ((%398 ((%31 %390) ((%32 %159) %33))) %107)) %269))
       ((%5 ((%168 ((%398 ((%31 %390) ((%32 %159) %33))) ((%18 ((%19 %394)
       %158)) %93))) %165)) ((%168 ((%398 ((%31 %141) ((%32 %140) ((%52
       %214) %215)))) %418)) %269)))`)
  val doReduce_ind =
    DT(["DISK_THM"], [],
       `(%685 (\%686. ((%14 ((%5 (%513 (\%460. (%135 (\%136. (%7 (\%379.
       (%557 (\%471. (%407 (\%687. ((($5 $4) ((%498 ((%52 $3) $2)) ((%499
       $1) %492))) $0)))))))))))) ((%5 (%513 (\%460. (%688 (\%689. (%407
       (\%690. ((($3 $2) ((%498 %33) $1)) $0)))))))) (%513 (\%460. (%135
       (\%136. (%7 (\%379. (%557 (\%471. (%135 (\%137. (%45 (\%152. (%176
       (\%475. (%407 (\%464. ((($8 $7) ((%498 ((%52 $6) $5)) ((%499 $4)
       ((%179 ((%180 $3) $2)) $1)))) $0)))))))))))))))))))) (%513 (\%691.
       (%7 (\%540. (%557 (\%692. (%176 (\%693. (%407 (\%694. ((($5 $4)
       ((%498 $3) ((%499 $2) $1))) $0))))))))))))))`)
  val doReduce_def =
    DT(["DISK_THM"], [],
       `((%518 (((%519 %460) ((%498 ((%52 %136) %379)) ((%499 %471) ((%179
       ((%180 %137) %152)) %475)))) %464)) (((%478 (%479 %136)) %480)
       ((%481 ((%482 (\%13. (\%8. ((%483 (\%484. (((%485 %480) (\%486.
       ((%487 (\%488. ((%489 (\%490. (((%478 ((%491 $0) %492)) %480) ((%493
       (\%494. ((%495 (\%496. (%497 ((%498 ((%52 %136) %379)) ((%499 ((%500
       ((%501 ((%502 $0) $4)) %503)) $3)) ((%504 $2) $0)))))) ((%180 (%55
       $6)) (((%505 %460) $0) (%55 $6)))))) (%506 (%507 $0)))))) ((%508
       ((%179 ((%180 %137) %152)) %475)) (%232 $3))))) ((%509 %471) (%232
       $2))))) $0))) ((%510 %471) %464))))) (%511 %464))) (%512 %464))))`)
  val parse_ind =
    DT(["DISK_THM"], [],
       `(%695 (\%696. ((%14 ((%5 (%551 (\%531. (%7 (\%533. (%557 (\%471.
       (($3 $2) ((%498 $1) ((%499 $0) %492)))))))))) (%551 (\%531. (%7
       (\%533. (%557 (\%471. (%135 (\%137. (%45 (\%152. (%176 (\%475. (($6
       $5) ((%498 $4) ((%499 $3) ((%179 ((%180 $2) $1))
       $0)))))))))))))))))) (%551 (\%697. (%7 (\%540. (%557 (\%692. (%176
       (\%693. (($4 $3) ((%498 $2) ((%499 $1) $0))))))))))))))`)
  val parse_def =
    DT(["DISK_THM"], [],
       `((%518 ((%553 %531) ((%498 %533) ((%499 %471) ((%179 ((%180 %137)
       %152)) %475))))) (((%537 %480) (\%538. (((%468 %480) (\%539. (\%540.
       (((%468 ((%541 (\%542. ((((%543 (\%464. (((%544 $4) ((%498 ((%52 $3)
       %33)) ((%499 %471) ((%179 ((%180 %137) %152)) %475)))) $0))) (\%545.
       %480)) %480) $0))) (((%430 $2) %152) $1))) (\%546. (\%547. ((%541
       (\%542. ((((%543 (\%464. (((%544 $6) ((%498 ((%52 $5) ((%52 $3)
       $2))) ((%499 %471) ((%179 ((%180 %137) %152)) %475)))) $0))) (\%545.
       (((%478 (%479 $5)) %480) (%497 ((%498 ((%52 $3) $2)) ((%499 ((%501
       ((%502 $0) (%548 (%549 (%550 $5))))) %471)) ((%504 ((%179 ((%180
       %137) %152)) %475)) $0))))))) %480) $0))) (((%430 $4) %152) $3)))))
       $0)))) %533))) %531))`)
  end
  val _ = DB.bindl "yaccDef"
  [("getItems_tupled_primitive_def",getItems_tupled_primitive_def,DB.Def),
   ("getItems_curried_def",getItems_curried_def,DB.Def),
   ("iclosure1_tupled_primitive_def",
    iclosure1_tupled_primitive_def,
    DB.Def), ("iclosure1_curried_def",iclosure1_curried_def,DB.Def),
   ("iclosure_defn_tupled_primitive_def",
    iclosure_defn_tupled_primitive_def,
    DB.Def),
   ("iclosure_defn_curried_def",iclosure_defn_curried_def,DB.Def),
   ("rules2Items_primitive_def",rules2Items_primitive_def,DB.Def),
   ("auggr_def",auggr_def,DB.Def),
   ("initProds2Items_tupled_primitive_def",
    initProds2Items_tupled_primitive_def,
    DB.Def),
   ("initProds2Items_curried_def",initProds2Items_curried_def,DB.Def),
   ("initItems_def",initItems_def,DB.Def),
   ("moveDot_tupled_primitive_def",moveDot_tupled_primitive_def,DB.Def),
   ("moveDot_curried_def",moveDot_curried_def,DB.Def),
   ("nextState_def",nextState_def,DB.Def),
   ("validItl_tupled_primitive_def",validItl_tupled_primitive_def,DB.Def),
   ("validItl_curried_def",validItl_curried_def,DB.Def),
   ("validStates_tupled_primitive_def",
    validStates_tupled_primitive_def,
    DB.Def), ("validStates_curried_def",validStates_curried_def,DB.Def),
   ("sgoto_def",sgoto_def,DB.Def),
   ("reduce_tupled_primitive_def",reduce_tupled_primitive_def,DB.Def),
   ("reduce_curried_def",reduce_curried_def,DB.Def),
   ("buildTree_def",buildTree_def,DB.Def),
   ("addRule_def",addRule_def,DB.Def), ("machine_def",machine_def,DB.Def),
   ("slr_def",slr_def,DB.Def),
   ("ruleItems_defn_primitive_def",ruleItems_defn_primitive_def,DB.Def),
   ("itemPair_def",itemPair_def,DB.Def),
   ("allItems_primitive_def",allItems_primitive_def,DB.Def),
   ("symNeighbour_def",symNeighbour_def,DB.Def),
   ("asNeighbours_def",asNeighbours_def,DB.Def),
   ("visit_defn_tupled_primitive_def",
    visit_defn_tupled_primitive_def,
    DB.Def), ("visit_defn_curried_def",visit_defn_curried_def,DB.Def),
   ("validItem_tupled_primitive_def",
    validItem_tupled_primitive_def,
    DB.Def), ("validItem_curried_def",validItem_curried_def,DB.Def),
   ("isGrammarItl_def",isGrammarItl_def,DB.Def),
   ("allGrammarItls_def",allGrammarItls_def,DB.Def),
   ("itemLhs_def",itemLhs_def,DB.Def),
   ("itemFstRhs_def",itemFstRhs_def,DB.Def),
   ("itemSndRhs_def",itemSndRhs_def,DB.Def),
   ("slrML4Sym_def",slrML4Sym_def,DB.Def), ("slrML_def",slrML_def,DB.Def),
   ("findItemInRules_tupled_primitive_def",
    findItemInRules_tupled_primitive_def,
    DB.Def),
   ("findItemInRules_curried_def",findItemInRules_curried_def,DB.Def),
   ("itemEqRuleList_defn_tupled_primitive_def",
    itemEqRuleList_defn_tupled_primitive_def,
    DB.Def),
   ("itemEqRuleList_defn_curried_def",
    itemEqRuleList_defn_curried_def,
    DB.Def), ("getState_def",getState_def,DB.Def),
   ("doReduce_tupled_primitive_def",doReduce_tupled_primitive_def,DB.Def),
   ("doReduce_curried_def",doReduce_curried_def,DB.Def),
   ("parse_tupled_primitive_def",parse_tupled_primitive_def,DB.Def),
   ("parse_curried_def",parse_curried_def,DB.Def),
   ("parser_def",parser_def,DB.Def), ("yacc_def",yacc_def,DB.Def),
   ("getItems_ind",getItems_ind,DB.Thm),
   ("getItems_def",getItems_def,DB.Thm),
   ("iclosure1_ind",iclosure1_ind,DB.Thm),
   ("iclosure1_def",iclosure1_def,DB.Thm),
   ("rules2Items_ind",rules2Items_ind,DB.Thm),
   ("rules2Items_def",rules2Items_def,DB.Thm),
   ("iclosure1_mem",iclosure1_mem,DB.Thm),
   ("iclosure1_not_nil",iclosure1_not_nil,DB.Thm),
   ("iclosure1_len",iclosure1_len,DB.Thm),
   ("rules2items_sub",rules2items_sub,DB.Thm),
   ("iclosure1_outmem",iclosure1_outmem,DB.Thm),
   ("iclosure1_before_after_len",iclosure1_before_after_len,DB.Thm),
   ("iclosure",iclosure,DB.Thm), ("iclosure_ind",iclosure_ind,DB.Thm),
   ("iclosure_nil",iclosure_nil,DB.Thm),
   ("ag_new_rule",ag_new_rule,DB.Thm),
   ("initProds2Items_ind",initProds2Items_ind,DB.Thm),
   ("initProds2Items_def",initProds2Items_def,DB.Thm),
   ("moveDot_ind",moveDot_ind,DB.Thm), ("moveDot_def",moveDot_def,DB.Thm),
   ("validItl_ind",validItl_ind,DB.Thm),
   ("validItl_def",validItl_def,DB.Thm),
   ("validStates_ind",validStates_ind,DB.Thm),
   ("validStates_def",validStates_def,DB.Thm),
   ("validItl_append",validItl_append,DB.Thm),
   ("validStates_append",validStates_append,DB.Thm),
   ("validStates_pop",validStates_pop,DB.Thm),
   ("validItl_md",validItl_md,DB.Thm),
   ("validItl_rules_cons",validItl_rules_cons,DB.Thm),
   ("rules2items_sub2",rules2items_sub2,DB.Thm),
   ("validItl_mem",validItl_mem,DB.Thm),
   ("validItl_getItems",validItl_getItems,DB.Thm),
   ("validItl_iclosure1",validItl_iclosure1,DB.Thm),
   ("validItl_delete",validItl_delete,DB.Thm),
   ("validItl_rmDupes",validItl_rmDupes,DB.Thm),
   ("validItl_iclosure",validItl_iclosure,DB.Thm),
   ("validItl_sgoto",validItl_sgoto,DB.Thm),
   ("reduce_ind",reduce_ind,DB.Thm), ("reduce_def",reduce_def,DB.Thm),
   ("allItems_ind",allItems_ind,DB.Thm),
   ("allItems_def",allItems_def,DB.Thm),
   ("validItem_ind",validItem_ind,DB.Thm),
   ("validItem_def",validItem_def,DB.Thm),
   ("finite_allItems",finite_allItems,DB.Thm),
   ("validItemRulesEqGrRules",validItemRulesEqGrRules,DB.Thm),
   ("allItems_append",allItems_append,DB.Thm),
   ("ruleItems_mem",ruleItems_mem,DB.Thm),
   ("allMemRuleItems",allMemRuleItems,DB.Thm),
   ("memRuleAllItems",memRuleAllItems,DB.Thm),
   ("itemEqRule",itemEqRule,DB.Thm),
   ("memAllItemsRules",memAllItemsRules,DB.Thm),
   ("validItemEqAllItems",validItemEqAllItems,DB.Thm),
   ("finite_validItem",finite_validItem,DB.Thm),
   ("finiteAllGrItls",finiteAllGrItls,DB.Thm),
   ("prop_mem",prop_mem,DB.Thm), ("validItl_evmem",validItl_evmem,DB.Thm),
   ("validItl_symNeighbour",validItl_symNeighbour,DB.Thm),
   ("symNeighbour_allDistinct",symNeighbour_allDistinct,DB.Thm),
   ("ar1",ar1,DB.Thm), ("findItemInRules_ind",findItemInRules_ind,DB.Thm),
   ("findItemInRules_def",findItemInRules_def,DB.Thm),
   ("doReduce_ind",doReduce_ind,DB.Thm),
   ("doReduce_def",doReduce_def,DB.Thm), ("parse_ind",parse_ind,DB.Thm),
   ("parse_def",parse_def,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("followSetDefTheory.followSetDef_grammars",
                          followSetDefTheory.followSetDef_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "getItems_tupled")
        {Name = "getItems_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getItems")
        {Name = "getItems", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "iclosure1_tupled")
        {Name = "iclosure1_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "iclosure1")
        {Name = "iclosure1", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "iclosure_defn_tupled")
        {Name = "iclosure_defn_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "iclosure")
        {Name = "iclosure", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rules2Items")
        {Name = "rules2Items", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "auggr")
        {Name = "auggr", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "initProds2Items_tupled")
        {Name = "initProds2Items_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "initProds2Items")
        {Name = "initProds2Items", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "initItems")
        {Name = "initItems", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "moveDot_tupled")
        {Name = "moveDot_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "moveDot")
        {Name = "moveDot", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nextState")
        {Name = "nextState", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validItl_tupled")
        {Name = "validItl_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validItl")
        {Name = "validItl", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validStates_tupled")
        {Name = "validStates_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validStates")
        {Name = "validStates", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "sgoto")
        {Name = "sgoto", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "reduce_tupled")
        {Name = "reduce_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "reduce")
        {Name = "reduce", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "buildTree")
        {Name = "buildTree", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "addRule")
        {Name = "addRule", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "machine")
        {Name = "machine", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "slr")
        {Name = "slr", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ruleItems")
        {Name = "ruleItems", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "itemPair")
        {Name = "itemPair", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "allItems")
        {Name = "allItems", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "symNeighbour")
        {Name = "symNeighbour", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "asNeighbours")
        {Name = "asNeighbours", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "visit_defn_tupled")
        {Name = "visit_defn_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "visit")
        {Name = "visit", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validItem_tupled")
        {Name = "validItem_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validItem")
        {Name = "validItem", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isGrammarItl")
        {Name = "isGrammarItl", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "allGrammarItls")
        {Name = "allGrammarItls", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "itemLhs")
        {Name = "itemLhs", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "itemFstRhs")
        {Name = "itemFstRhs", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "itemSndRhs")
        {Name = "itemSndRhs", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "slrML4Sym")
        {Name = "slrML4Sym", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "slrML")
        {Name = "slrML", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "findItemInRules_tupled")
        {Name = "findItemInRules_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "findItemInRules")
        {Name = "findItemInRules", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "itemEqRuleList_defn_tupled")
        {Name = "itemEqRuleList_defn_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "itemEqRuleList")
        {Name = "itemEqRuleList", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getState")
        {Name = "getState", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "doReduce_tupled")
        {Name = "doReduce_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "doReduce")
        {Name = "doReduce", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parse_tupled")
        {Name = "parse_tupled", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parse")
        {Name = "parse", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parser")
        {Name = "parser", Thy = "yaccDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "yacc")
        {Name = "yacc", Thy = "yaccDef"}
  val yaccDef_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [getItems_def];  
  
  val _ = computeLib.add_funs [iclosure1_def];  
  
  val _ = computeLib.add_funs [rules2Items_def];  
  
  val _ = computeLib.add_funs [auggr_def];  
  
  val _ = computeLib.add_funs [initProds2Items_def];  
  
  val _ = computeLib.add_funs [initItems_def];  
  
  val _ = computeLib.add_funs [moveDot_def];  
  
  val _ = computeLib.add_funs [nextState_def];  
  
  val _ = computeLib.add_funs [validItl_def];  
  
  val _ = computeLib.add_funs [validStates_def];  
  
  val _ = computeLib.add_funs [sgoto_def];  
  
  val _ = computeLib.add_funs [reduce_def];  
  
  val _ = computeLib.add_funs [buildTree_def];  
  
  val _ = computeLib.add_funs [addRule_def];  
  
  val _ = computeLib.add_funs [machine_def];  
  
  val _ = computeLib.add_funs [slr_def];  
  
  val _ = computeLib.add_funs [itemPair_def];  
  
  val _ = computeLib.add_funs [allItems_def];  
  
  val _ = computeLib.add_funs [symNeighbour_def];  
  
  val _ = computeLib.add_funs [asNeighbours_def];  
  
  val _ = computeLib.add_funs [validItem_def];  
  
  val _ = computeLib.add_funs [isGrammarItl_def];  
  
  val _ = computeLib.add_funs [allGrammarItls_def];  
  
  val _ = computeLib.add_funs [itemLhs_def];  
  
  val _ = computeLib.add_funs [itemFstRhs_def];  
  
  val _ = computeLib.add_funs [itemSndRhs_def];  
  
  val _ = computeLib.add_funs [slrML4Sym_def];  
  
  val _ = computeLib.add_funs [slrML_def];  
  
  val _ = computeLib.add_funs [findItemInRules_def];  
  
  val _ = computeLib.add_funs [getState_def];  
  
  val _ = computeLib.add_funs [doReduce_def];  
  
  val _ = computeLib.add_funs [parse_def];  
  
  val _ = computeLib.add_funs [parser_def];  
  
  val _ = computeLib.add_funs [yacc_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
