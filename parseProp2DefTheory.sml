structure parseProp2DefTheory :> parseProp2DefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading parseProp2DefTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open yaccDefTheory
  in end;
  val _ = Theory.link_parents
          ("parseProp2Def",
          Arbnum.fromString "1203551256",
          Arbnum.fromString "874748")
          [("yaccDef",
           Arbnum.fromString "1203551220",
           Arbnum.fromString "599001")];
  val _ = Theory.incorporate_types "parseProp2Def" [];
  val _ = Theory.incorporate_consts "parseProp2Def"
     [("stacktreeleaves",
       ((T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("prop2",
       ((T"list" "list" [T"symbol" "regexp" []] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list"
            [T"prod" "pair"
              [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
           bool)))))];
  
  local
  val share_table = Vector.fromList
  [C"=" "min"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> T"list" "list" [T"symbol" "regexp" []]) -->
      ((T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        T"list" "list" [T"symbol" "regexp" []]) --> bool))),
   C"stacktreeleaves" "parseProp2Def"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      --> T"list" "list" [T"symbol" "regexp" []])),
   C"WFREC" "relation"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool))
      -->
      (((T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         T"list" "list" [T"symbol" "regexp" []]) -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"@" "min"
    ((((T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool))
       --> bool) -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        bool)))),
   V"R"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool))), C"/\\" "bool" ((bool --> (bool --> bool))),
   C"WF" "relation"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool))
      --> bool)),
   C"!" "bool" (((T"ptree" "parseTree" [] --> bool) --> bool)),
   V"tree" (T"ptree" "parseTree" []),
   C"!" "bool"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   V"itl" (T"list" "list" [T"item" "parserDef" []]),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"sym" (T"symbol" "regexp" []),
   C"!" "bool"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool) --> bool)),
   V"rst"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
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
   C"state" "parserDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"state" "parserDef" []))),
   V"stacktreeleaves"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      --> T"list" "list" [T"symbol" "regexp" []])),
   V"a"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"list_case" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
        -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"I" "combin"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   V"v"
    (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]),
   C"pair_case" "pair"
    (((T"state" "parserDef" [] -->
       (T"ptree" "parseTree" [] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
       --> T"list" "list" [T"symbol" "regexp" []]))),
   V"v2" (T"state" "parserDef" []),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"state" "parserDef" [] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"APPEND" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"leaves" "parseTree"
    ((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"orig" (T"list" "list" [T"symbol" "regexp" []]),
   V"sl" (T"list" "list" [T"symbol" "regexp" []]),
   V"stl"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"prop2" "parseProp2Def"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        bool)))),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"!" "bool"
    ((((T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool)
       --> bool) --> bool)),
   V"P"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      --> bool)), C"==>" "min" ((bool --> (bool --> bool))),
   C"NIL" "list"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"v"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       bool) --> bool)),
   V"p" (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"l" (T"string" "string" []),
   V"r" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"nonTerminal" "parseTree" [] --> bool) --> bool)),
   V"nt" (T"nonTerminal" "parseTree" []),
   C"!" "bool"
    (((T"list" "list" [T"ptree" "parseTree" []] --> bool) --> bool)),
   V"ptl" (T"list" "list" [T"ptree" "parseTree" []]),
   C"=" "min"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      (T"option" "option" [T"ptree" "parseTree" []] --> bool))),
   C"addRule" "yaccDef"
    ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
      (T"rule" "grammarDef" [] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   C"SOME" "option"
    ((T"ptree" "parseTree" [] -->
      T"option" "option" [T"ptree" "parseTree" []])),
   C"Node" "parseTree"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []))),
   C"=" "min"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> bool))),
   C"REVERSE" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"ptree" "parseTree" []])),
   C"MAP" "list"
    (((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []) -->
      (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"SND" "pair"
    ((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
      T"ptree" "parseTree" [])),
   C"THE" "option"
    ((T"option" "option"
       [T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]]
      -->
      T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]])),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       T"option" "option"
        [T"list" "list"
          [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]]))),
   C"LENGTH" "list"
    ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" [])),
   V"x" (T"ptree" "parseTree" []), C"~" "bool" ((bool --> bool)),
   C"isLeaf" "parseTree" ((T"ptree" "parseTree" [] --> bool)),
   V"l1"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"l2"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
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
   V"l"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"n" (T"nonTerminal" "parseTree" []),
   C"MAP" "list"
    (((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
       --> T"ptree" "parseTree" []) -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> T"list" "list" [T"ptree" "parseTree" []]))),
   C"SND" "pair"
    ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []] -->
      T"ptree" "parseTree" [])),
   V"sl"
    (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C">=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"LENGTH" "list"
    ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
      T"num" "num" [])),
   V"stl"
    (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C"APPEND" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"pop" "listLemmas"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"num" "num" [] --> T"list" "list" [T"ptree" "parseTree" []]))),
   C"FLAT" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"MAP" "list"
    (((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
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
   V"m"
    (T"prod" "pair"
      [(T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])), alpha]),
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
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"rst" (T"list" "list" [T"symbol" "regexp" []]),
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
   C"CONS" "list"
    ((T"state" "parserDef" [] -->
      (T"list" "list" [T"state" "parserDef" []] -->
       T"list" "list" [T"state" "parserDef" []]))),
   V"s" (T"symbol" "regexp" []),
   V"csl" (T"list" "list" [T"state" "parserDef" []]),
   V"r" (T"rule" "grammarDef" []),
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
   V"sl'" (T"list" "list" [T"symbol" "regexp" []]),
   V"stl'"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"csl'" (T"list" "list" [T"state" "parserDef" []]),
   C"REVERSE" "list"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      T"list" "list"
       [T"prod" "pair"
         [T"state" "parserDef" [], T"ptree" "parseTree" []]])),
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
   V"m"
    (T"option" "option"
      [T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))]]),
   C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"g" (T"grammar" "grammarDef" []),
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
             T"list" "list" [T"state" "parserDef" []]]]])))]
  val DT = Thm.disk_thm share_table
  in
  val stacktreeleaves_primitive_def =
    DT([], [],
       `((%0 %1) ((%2 (%3 (\%4. ((%5 (%6 $0)) (%7 (\%8. (%9 (\%10. (%11
       (\%12. (%13 (\%14. (($4 $0) ((%15 ((%16 ((%17 $1) $2)) $3))
       $0)))))))))))))) (\%18. (\%19. (((%20 (%21 %22)) (\%23. (\%14. ((%24
       (\%25. (\%8. ((%26 (\%12. (\%10. (%21 ((%27 (%28 $2)) ($7 $4))))))
       $1)))) $1)))) $0)))))`)
  val prop2_def =
    DT([], [],
       `(%29 (\%30. (%29 (\%31. (%13 (\%32. ((%33 (((%34 $2) $1) $0)) ((%35
       ((%27 (%1 $0)) $1)) $2))))))))`)
  val stacktreeleaves_ind =
    DT(["DISK_THM"], [],
       `(%36 (\%37. ((%38 ((%5 ($0 %39)) (%11 (\%12. (%9 (\%10. (%7 (\%8.
       (%13 (\%14. ((%38 ($4 $0)) ($4 ((%15 ((%16 ((%17 $3) $2)) $1))
       $0))))))))))))) (%13 (\%40. ($1 $0))))))`)
  val stacktreeleaves_def =
    DT(["DISK_THM"], [],
       `((%5 ((%35 (%1 %39)) %22)) ((%35 (%1 ((%15 ((%16 ((%17 %12) %10))
       %8)) %14))) ((%27 (%28 %8)) (%1 %14))))`)
  val revTakeMap =
    DT(["DISK_THM"], [],
       `(%41 (\%42. (%43 (\%44. (%29 (\%45. (%46 (\%47. (%48 (\%49. ((%38
       ((%50 ((%51 $4) ((%52 $3) $2))) (%53 ((%54 $1) $0)))) ((%55 $0) (%56
       ((%57 %58) (%59 ((%60 (%61 $2)) $4))))))))))))))))`)
  val addrule_ntLf =
    DT(["DISK_THM"], [],
       `((%38 ((%50 ((%51 %42) ((%52 %44) %45))) (%53 %62))) (%63 (%64
       %62)))`)
  val stl_append =
    DT(["DISK_THM"], [],
       `(%13 (\%65. (%13 (\%66. ((%35 (%1 ((%67 $1) $0))) ((%27 (%1 $1))
       (%1 $0)))))))`)
  val stl_map =
    DT(["DISK_THM"], [],
       `(%13 (\%68. ((%35 (%1 $0)) (%28 ((%54 %69) ((%70 %71) $0))))))`)
  val addrule_len =
    DT(["DISK_THM"], [],
       `((%38 ((%50 ((%51 %72) ((%52 %44) %45))) (%53 %62))) ((%73 (%74
       %72)) (%61 %45)))`)
  val addrule_leaves =
    DT(["DISK_THM"], [],
       `((%38 ((%50 ((%51 %75) ((%52 %44) %45))) (%53 ((%54 %47) %49))))
       ((%55 ((%57 %58) %75)) ((%76 (%56 %49)) ((%77 ((%57 %58) %75)) (%61
       %45)))))`)
  val stlEq =
    DT(["DISK_THM"], [],
       `(%13 (\%32. ((%35 (%1 $0)) (%78 ((%79 %28) ((%70 %71) $0))))))`)
  val red_stkleaves =
    DT(["DISK_THM"], [],
       `((%38 ((%80 (((%81 %82) ((%83 ((%84 %12) %85)) ((%86 %32) ((%87
       ((%17 %88) %10)) %89)))) %90)) (%91 ((%83 %92) ((%86 %93) %94)))))
       ((%35 (%1 (%95 %32))) (%1 (%95 %93))))`)
  val red_sym =
    DT(["DISK_THM"], [],
       `((%38 ((%80 (((%81 %82) ((%83 ((%84 %12) %85)) ((%86 %32) ((%87
       ((%17 %88) %10)) %89)))) %90)) (%91 ((%83 %92) ((%86 %93) %94)))))
       ((%35 %92) ((%84 %12) %85)))`)
  val prop2thm =
    DT(["DISK_THM"], [],
       `(%96 (\%97. (%98 (\%99. ((%38 ((%100 $1) (%101 $0))) ((%38 (((%34
       %30) %31) (%95 %32))) ((%38 ((%80 ((%102 $1) ((%83 %31) ((%86 %32)
       ((%87 ((%17 %88) %10)) %89))))) (%91 ((%83 %92) ((%86 %93) %94)))))
       (((%34 %30) %92) (%95 %93)))))))))`)
  end
  val _ = DB.bindl "parseProp2Def"
  [("stacktreeleaves_primitive_def",stacktreeleaves_primitive_def,DB.Def),
   ("prop2_def",prop2_def,DB.Def),
   ("stacktreeleaves_ind",stacktreeleaves_ind,DB.Thm),
   ("stacktreeleaves_def",stacktreeleaves_def,DB.Thm),
   ("revTakeMap",revTakeMap,DB.Thm), ("addrule_ntLf",addrule_ntLf,DB.Thm),
   ("stl_append",stl_append,DB.Thm), ("stl_map",stl_map,DB.Thm),
   ("addrule_len",addrule_len,DB.Thm),
   ("addrule_leaves",addrule_leaves,DB.Thm), ("stlEq",stlEq,DB.Thm),
   ("red_stkleaves",red_stkleaves,DB.Thm), ("red_sym",red_sym,DB.Thm),
   ("prop2thm",prop2thm,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("yaccDefTheory.yaccDef_grammars",
                          yaccDefTheory.yaccDef_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "stacktreeleaves")
        {Name = "stacktreeleaves", Thy = "parseProp2Def"}
  val _ = update_grms
       (temp_overload_on_by_nametype "prop2")
        {Name = "prop2", Thy = "parseProp2Def"}
  val parseProp2Def_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [stacktreeleaves_def];  
  
  val _ = computeLib.add_funs [prop2_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
