structure parseProp1DefTheory :> parseProp1DefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading parseProp1DefTheory ... " else ()
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
          ("parseProp1Def",
          Arbnum.fromString "1203551273",
          Arbnum.fromString "418732")
          [("yaccDef",
           Arbnum.fromString "1203551220",
           Arbnum.fromString "599001")];
  val _ = Theory.incorporate_types "parseProp1Def" [];
  val _ = Theory.incorporate_consts "parseProp1Def"
     [("stackltmnls",
       ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         --> T"list" "list" [T"symbol" "regexp" []]))),
      ("stacklsymtree",
       ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         -->
         T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))),
      ("prop1",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list"
           [T"prod" "pair"
             [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
          bool)))),
      ("validStkSymTree",
       ((T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
         bool))),
      ("stacklntmnls",
       ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         --> T"list" "list" [T"symbol" "regexp" []])))];
  
  local
  val share_table = Vector.fromList
  [C"=" "min"
    (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       T"list" "list" [T"symbol" "regexp" []]) -->
      ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> T"list" "list" [T"symbol" "regexp" []]) --> bool))),
   C"stacklntmnls" "parseProp1Def"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"WFREC" "relation"
    (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> bool)) -->
      (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         --> T"list" "list" [T"symbol" "regexp" []]) -->
        (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         --> T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> T"list" "list" [T"symbol" "regexp" []])))),
   C"@" "min"
    ((((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        -->
        (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         --> bool)) --> bool) -->
      (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> bool)))),
   V"R"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       bool))), C"/\\" "bool" ((bool --> (bool --> bool))),
   C"WF" "relation"
    (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> bool)) --> bool)), C"!" "bool" (((alpha --> bool) --> bool)),
   V"tree" (alpha),
   C"!" "bool"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   V"itl" (T"list" "list" [T"item" "parserDef" []]),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       bool) --> bool)),
   V"rst"
    (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"sym" (T"symbol" "regexp" []),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"isNonTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   C"CONS" "list"
    ((T"prod" "pair" [T"state" "parserDef" [], alpha] -->
      (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]))),
   C"," "pair"
    ((T"state" "parserDef" [] -->
      (alpha --> T"prod" "pair" [T"state" "parserDef" [], alpha]))),
   C"state" "parserDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"state" "parserDef" []))), C"~" "bool" ((bool --> bool)),
   V"stacklntmnls"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   V"a" (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]),
   C"list_case" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      ((T"prod" "pair" [T"state" "parserDef" [], alpha] -->
        (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         --> T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> T"list" "list" [T"symbol" "regexp" []])))),
   C"I" "combin"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   V"v" (T"prod" "pair" [T"state" "parserDef" [], alpha]),
   C"pair_case" "pair"
    (((T"state" "parserDef" [] -->
       (alpha --> T"list" "list" [T"symbol" "regexp" []])) -->
      (T"prod" "pair" [T"state" "parserDef" [], alpha] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"v2" (T"state" "parserDef" []),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"state" "parserDef" [] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"stackltmnls" "parseProp1Def"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"isTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   V"stackltmnls"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"=" "min"
    (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]) -->
      ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])
       --> bool))),
   C"stacklsymtree" "parseProp1Def"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])),
   C"WFREC" "relation"
    (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> bool)) -->
      (((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         -->
         T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])
        -->
        (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         -->
         T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))
       -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        -->
        T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])))),
   V"stacklsymtree"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])),
   C"list_case" "list"
    ((T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
      ((T"prod" "pair" [T"state" "parserDef" [], alpha] -->
        (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
         -->
         T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))
       -->
       (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        -->
        T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])))),
   C"I" "combin"
    ((T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
      T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]])),
   C"NIL" "list"
    (T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]),
   C"pair_case" "pair"
    (((T"state" "parserDef" [] -->
       (alpha -->
        T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))
      -->
      (T"prod" "pair" [T"state" "parserDef" [], alpha] -->
       T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))
      -->
      (T"state" "parserDef" [] -->
       T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))),
   C"CONS" "list"
    ((T"prod" "pair" [T"symbol" "regexp" [], alpha] -->
      (T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
       T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (alpha --> T"prod" "pair" [T"symbol" "regexp" [], alpha]))),
   C"=" "min"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool) -->
      ((T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool)
       --> bool))),
   C"validStkSymTree" "parseProp1Def"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      --> bool)),
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
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool)
        -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool))
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        bool)))),
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
       --> bool))),
   C"WF" "relation"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool))
      --> bool)),
   C"!" "bool"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool) --> bool)),
   V"rst"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"!" "bool" (((T"ptree" "parseTree" [] --> bool) --> bool)),
   V"tree" (T"ptree" "parseTree" []),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"ptree2Sym" "parseTree"
    ((T"ptree" "parseTree" [] --> T"symbol" "regexp" [])),
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
   V"validStkSymTree"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      --> bool)),
   V"a"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"list_case" "list"
    ((bool -->
      ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
        -->
        (T"list" "list"
          [T"prod" "pair"
            [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool))
       -->
       (T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] -->
        bool)))), C"I" "combin" ((bool --> bool)), C"T" "bool" (bool),
   V"v"
    (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]),
   C"pair_case" "pair"
    (((T"state" "parserDef" [] --> (T"ptree" "parseTree" [] --> bool)) -->
      (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
       --> bool))),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] --> bool)) -->
      (T"state" "parserDef" [] --> bool))),
   C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"g" (T"grammar" "grammarDef" []),
   V"stl"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"prop1" "parseProp1Def"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool))), V"s" (T"symbol" "regexp" []),
   V"t" (T"ptree" "parseTree" []),
   C"MEM" "list"
    ((T"prod" "pair" [T"symbol" "regexp" [], T"ptree" "parseTree" []] -->
      (T"list" "list"
        [T"prod" "pair" [T"symbol" "regexp" [], T"ptree" "parseTree" []]]
       --> bool))),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (T"ptree" "parseTree" [] -->
       T"prod" "pair" [T"symbol" "regexp" [], T"ptree" "parseTree" []]))),
   C"stacklsymtree" "parseProp1Def"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      T"list" "list"
       [T"prod" "pair" [T"symbol" "regexp" [], T"ptree" "parseTree" []]])),
   C"validptree" "parseTree"
    ((T"grammar" "grammarDef" [] --> (T"ptree" "parseTree" [] --> bool))),
   C"!" "bool"
    ((((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]
        --> bool) --> bool) --> bool)),
   V"P"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      bool)),
   C"NIL" "list"
    (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]),
   V"v" (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"=" "min"
    ((T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
      (T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
       bool))),
   C"!" "bool"
    ((((T"list" "list"
         [T"prod" "pair"
           [T"state" "parserDef" [], T"ptree" "parseTree" []]] --> bool)
       --> bool) --> bool)),
   V"P"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      --> bool)),
   C"NIL" "list"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"v"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"l1"
    (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]),
   V"l2"
    (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]),
   C"APPEND" "list"
    ((T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
      (T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]] -->
       T"list" "list" [T"prod" "pair" [T"state" "parserDef" [], alpha]]))),
   C"APPEND" "list"
    ((T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
      (T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
       T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]]))),
   C"!" "bool"
    (((T"prod" "pair" [T"symbol" "regexp" [], alpha] --> bool) --> bool)),
   V"e" (T"prod" "pair" [T"symbol" "regexp" [], alpha]),
   C"MEM" "list"
    ((T"prod" "pair" [T"symbol" "regexp" [], alpha] -->
      (T"list" "list" [T"prod" "pair" [T"symbol" "regexp" [], alpha]] -->
       bool))), C"\\/" "bool" ((bool --> (bool --> bool))),
   V"l"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"st" (alpha), V"pt" (T"ptree" "parseTree" []),
   C"MEM" "list"
    ((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []] -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool))),
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
   V"l1"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"l2"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"?" "bool"
    (((T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool) --> bool)),
   V"pfx"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   V"sfx"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"=" "min"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"list" "list"
        [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
       --> bool))),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       bool) --> bool)),
   V"p" (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"l" (T"list" "list" [T"symbol" "regexp" []]),
   C"?" "bool"
    (((T"list" "list" [T"ptree" "parseTree" []] --> bool) --> bool)),
   V"x" (T"list" "list" [T"ptree" "parseTree" []]),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
      (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
       bool))),
   C"buildTree" "yaccDef"
    ((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]))),
   C"SOME" "option"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]])),
   C"=" "min"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> bool))),
   C"NIL" "list" (T"list" "list" [T"ptree" "parseTree" []]), V"l" (alpha),
   V"r" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((beta --> bool) --> bool)), V"g" (beta),
   C"buildTree" "yaccDef"
    ((T"list" "list" [T"prod" "pair" [gamma, T"ptree" "parseTree" []]] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]))),
   V"p" (T"list" "list" [T"prod" "pair" [gamma, T"ptree" "parseTree" []]]),
   C"REVERSE" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"getSymbols" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"symbol" "regexp" []])), V"e" (alpha),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [beta, alpha]] --> bool) --> bool)),
   V"p" (T"list" "list" [T"prod" "pair" [beta, alpha]]),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool))),
   C"MAP" "list"
    (((T"prod" "pair" [beta, alpha] --> alpha) -->
      (T"list" "list" [T"prod" "pair" [beta, alpha]] -->
       T"list" "list" [alpha]))),
   C"SND" "pair" ((T"prod" "pair" [beta, alpha] --> alpha)),
   C"?" "bool" (((beta --> bool) --> bool)), V"f" (beta),
   C"MEM" "list"
    ((T"prod" "pair" [beta, alpha] -->
      (T"list" "list" [T"prod" "pair" [beta, alpha]] --> bool))),
   C"," "pair" ((beta --> (alpha --> T"prod" "pair" [beta, alpha]))),
   V"e" (T"ptree" "parseTree" []),
   C"MEM" "list"
    ((T"ptree" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> bool))),
   C"?" "bool" (((alpha --> bool) --> bool)), V"f" (alpha),
   C"MEM" "list"
    ((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
      (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       bool))),
   C"," "pair"
    ((alpha -->
      (T"ptree" "parseTree" [] -->
       T"prod" "pair" [alpha, T"ptree" "parseTree" []]))),
   V"x'" (T"list" "list" [T"ptree" "parseTree" []]),
   V"p"
    (T"list" "list"
      [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]),
   C"!" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   V"ru" (T"rule" "grammarDef" []),
   C"MEM" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"rules" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"=" "min"
    ((T"option" "option" [T"ptree" "parseTree" []] -->
      (T"option" "option" [T"ptree" "parseTree" []] --> bool))),
   C"addRule" "yaccDef"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"rule" "grammarDef" [] -->
       T"option" "option" [T"ptree" "parseTree" []]))),
   C"SOME" "option"
    ((T"ptree" "parseTree" [] -->
      T"option" "option" [T"ptree" "parseTree" []])),
   V"x" (T"ptree" "parseTree" []),
   C"=" "min"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"sgoto" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"symbol" "regexp" [] -->
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
       T"item" "parserDef" []))), V"s'" (T"string" "string" []),
   V"p"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   V"s" (T"string" "string" []),
   C"NIL" "list" (T"list" "list" [T"item" "parserDef" []]),
   C"IN" "bool"
    ((T"symbol" "regexp" [] -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   V"sym" (T"string" "string" []),
   C"followSetML" "followSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool)))),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"=" "min"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"reduce" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       (T"string" "string" [] -->
        T"list" "list" [T"rule" "grammarDef" []])))),
   C"," "pair"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]]))),
   V"q" (T"list" "list" [T"symbol" "regexp" []]),
   C"CONS" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   C"APPEND" "list"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"list" "list" [T"item" "parserDef" []]))),
   V"l1" (T"list" "list" [T"item" "parserDef" []]),
   V"l2" (T"list" "list" [T"item" "parserDef" []]),
   C"APPEND" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   C"!" "bool"
    (((T"list" "list" [T"rule" "grammarDef" []] --> bool) --> bool)),
   V"out" (T"list" "list" [T"rule" "grammarDef" []]),
   V"e" (T"rule" "grammarDef" []),
   C"?" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"l" (T"string" "string" []),
   C"?" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"r1" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min"
    ((T"rule" "grammarDef" [] --> (T"rule" "grammarDef" [] --> bool))),
   C"MEM" "list"
    ((T"item" "parserDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"!" "bool"
    (((T"prod" "pair"
        [(T"list" "list" [T"item" "parserDef" []] -->
          (T"symbol" "regexp" [] -->
           T"list" "list" [T"item" "parserDef" []])),
         (T"list" "list" [T"item" "parserDef" []] -->
          (T"string" "string" [] -->
           T"list" "list" [T"rule" "grammarDef" []]))] --> bool) -->
      bool)),
   V"m"
    (T"prod" "pair"
      [(T"list" "list" [T"item" "parserDef" []] -->
        (T"symbol" "regexp" [] -->
         T"list" "list" [T"item" "parserDef" []])),
       (T"list" "list" [T"item" "parserDef" []] -->
        (T"string" "string" [] -->
         T"list" "list" [T"rule" "grammarDef" []]))]),
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
   C"validItl" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
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
   C"REDUCE" "parserDef"
    ((T"rule" "grammarDef" [] --> T"action" "parserDef" [])),
   V"r" (T"rule" "grammarDef" []),
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
   V"csl" (T"list" "list" [T"state" "parserDef" []]),
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
   C"?" "bool"
    (((T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]
       --> bool) --> bool)),
   V"e"
    (T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"n" (T"num" "num" []),
   C"pop" "listLemmas"
    ((T"list" "list"
       [T"prod" "pair" [T"state" "parserDef" [], T"ptree" "parseTree" []]]
      -->
      (T"num" "num" [] -->
       T"list" "list"
        [T"prod" "pair"
          [T"state" "parserDef" [], T"ptree" "parseTree" []]]))),
   C"GOTO" "parserDef"
    ((T"state" "parserDef" [] --> T"action" "parserDef" [])),
   V"l" (T"list" "list" [T"item" "parserDef" []]),
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
             T"list" "list" [T"state" "parserDef" []]]]]))),
   V"sl" (T"list" "list" [T"symbol" "regexp" []]),
   C"NULL" "list" ((T"list" "list" [T"state" "parserDef" []] --> bool)),
   C"validStates" "yaccDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"state" "parserDef" []] --> bool)))]
  val DT = Thm.disk_thm share_table
  in
  val stacklntmnls_primitive_def =
    DT([], [],
       `((%0 %1) ((%2 (%3 (\%4. ((%5 (%6 $0)) ((%5 (%7 (\%8. (%9 (\%10.
       (%11 (\%12. (%13 (\%14. ((%15 (%16 $0)) (($4 $1) ((%17 ((%18 ((%19
       $0) $2)) $3)) $1)))))))))))) (%7 (\%8. (%9 (\%10. (%11 (\%12. (%13
       (\%14. ((%15 (%20 (%16 $0))) (($4 $1) ((%17 ((%18 ((%19 $0) $2))
       $3)) $1)))))))))))))))) (\%21. (\%22. (((%23 (%24 %25)) (\%26.
       (\%12. ((%27 (\%28. (\%8. ((%29 (\%14. (\%10. (%24 (((%30 (%16 $1))
       ((%31 $1) ($7 $4))) ($7 $4)))))) $1)))) $1)))) $0)))))`)
  val stackltmnls_primitive_def =
    DT([], [],
       `((%0 %32) ((%2 (%3 (\%4. ((%5 (%6 $0)) ((%5 (%7 (\%8. (%9 (\%10.
       (%11 (\%12. (%13 (\%14. ((%15 (%33 $0)) (($4 $1) ((%17 ((%18 ((%19
       $0) $2)) $3)) $1)))))))))))) (%7 (\%8. (%9 (\%10. (%11 (\%12. (%13
       (\%14. ((%15 (%20 (%33 $0))) (($4 $1) ((%17 ((%18 ((%19 $0) $2))
       $3)) $1)))))))))))))))) (\%34. (\%22. (((%23 (%24 %25)) (\%26.
       (\%12. ((%27 (\%28. (\%8. ((%29 (\%14. (\%10. (%24 (((%30 (%33 $1))
       ((%31 $1) ($7 $4))) ($7 $4)))))) $1)))) $1)))) $0)))))`)
  val stacklsymtree_primitive_def =
    DT([], [],
       `((%35 %36) ((%37 (%3 (\%4. ((%5 (%6 $0)) (%7 (\%8. (%9 (\%10. (%13
       (\%14. (%11 (\%12. (($4 $0) ((%17 ((%18 ((%19 $1) $2)) $3))
       $0)))))))))))))) (\%38. (\%22. (((%39 (%40 %41)) (\%26. (\%12. ((%42
       (\%28. (\%8. ((%43 (\%14. (\%10. (%40 ((%44 ((%45 $1) $2)) ($7
       $4)))))) $1)))) $1)))) $0)))))`)
  val validStkSymTree_primitive_def =
    DT([], [],
       `((%46 %47) ((%48 (%49 (\%50. ((%5 (%51 $0)) (%9 (\%10. (%52 (\%53.
       (%54 (\%55. (%13 (\%14. ((%15 ((%56 $0) (%57 $1))) (($4 $2) ((%58
       ((%59 ((%19 $0) $3)) $1)) $2))))))))))))))) (\%60. (\%61. (((%62
       (%63 %64)) (\%65. (\%53. ((%66 (\%28. (\%55. ((%67 (\%14. (\%10.
       (%63 ((%5 ((%56 $1) (%57 $2))) ($7 $4)))))) $1)))) $1)))) $0)))))`)
  val prop1_def =
    DT([], [],
       `(%68 (\%69. (%52 (\%70. ((%71 ((%72 $1) $0)) ((%5 (%47 $0)) (%13
       (\%73. (%54 (\%74. ((%15 ((%75 ((%76 $1) $0)) (%77 $2))) ((%15 (%16
       $1)) ((%78 $3) $0)))))))))))))`)
  val stacklntmnls_ind =
    DT(["DISK_THM"], [],
       `(%79 (\%80. ((%15 ((%5 ($0 %81)) (%13 (\%14. (%9 (\%10. (%7 (\%8.
       (%11 (\%12. ((%15 ((%5 ((%15 (%16 $3)) ($4 $0))) ((%15 (%20 (%16
       $3))) ($4 $0)))) ($4 ((%17 ((%18 ((%19 $3) $2)) $1)) $0)))))))))))))
       (%11 (\%82. ($1 $0))))))`)
  val stacklntmnls_def =
    DT(["DISK_THM"], [],
       `((%5 ((%83 (%1 %81)) %25)) ((%83 (%1 ((%17 ((%18 ((%19 %14) %10))
       %8)) %12))) (((%30 (%16 %14)) ((%31 %14) (%1 %12))) (%1 %12))))`)
  val stackltmnls_ind =
    DT(["DISK_THM"], [],
       `(%79 (\%80. ((%15 ((%5 ($0 %81)) (%13 (\%14. (%9 (\%10. (%7 (\%8.
       (%11 (\%12. ((%15 ((%5 ((%15 (%33 $3)) ($4 $0))) ((%15 (%20 (%33
       $3))) ($4 $0)))) ($4 ((%17 ((%18 ((%19 $3) $2)) $1)) $0)))))))))))))
       (%11 (\%82. ($1 $0))))))`)
  val stackltmnls_def =
    DT(["DISK_THM"], [],
       `((%5 ((%83 (%32 %81)) %25)) ((%83 (%32 ((%17 ((%18 ((%19 %14) %10))
       %8)) %12))) (((%30 (%33 %14)) ((%31 %14) (%32 %12))) (%32 %12))))`)
  val stacklsymtree_ind =
    DT(["DISK_THM"], [],
       `(%79 (\%80. ((%15 ((%5 ($0 %81)) (%13 (\%14. (%9 (\%10. (%7 (\%8.
       (%11 (\%12. ((%15 ($4 $0)) ($4 ((%17 ((%18 ((%19 $3) $2)) $1))
       $0))))))))))))) (%11 (\%82. ($1 $0))))))`)
  val stacklsymtree_def =
    DT(["DISK_THM"], [],
       `((%5 ((%84 (%36 %81)) %41)) ((%84 (%36 ((%17 ((%18 ((%19 %14) %10))
       %8)) %12))) ((%44 ((%45 %14) %8)) (%36 %12))))`)
  val validStkSymTree_ind =
    DT(["DISK_THM"], [],
       `(%85 (\%86. ((%15 ((%5 ($0 %87)) (%13 (\%14. (%9 (\%10. (%54 (\%55.
       (%52 (\%53. ((%15 ((%15 ((%56 $3) (%57 $1))) ($4 $0))) ($4 ((%58
       ((%59 ((%19 $3) $2)) $1)) $0))))))))))))) (%52 (\%88. ($1 $0))))))`)
  val validStkSymTree_def =
    DT(["DISK_THM"], [],
       `((%5 ((%71 (%47 %87)) %64)) ((%71 (%47 ((%58 ((%59 ((%19 %14) %10))
       %55)) %53))) ((%5 ((%56 %14) (%57 %55))) (%47 %53))))`)
  val slst_append =
    DT(["DISK_THM"], [],
       `(%11 (\%89. (%11 (\%90. ((%84 (%36 ((%91 $1) $0))) ((%92 (%36 $1))
       (%36 $0)))))))`)
  val slst_mem1 =
    DT(["DISK_THM"], [],
       `(%93 (\%94. (%11 (\%89. (%11 (\%90. ((%15 ((%95 $2) (%36 $1)))
       ((%95 $2) (%36 ((%91 $1) $0))))))))))`)
  val slst_mem2 =
    DT(["DISK_THM"], [],
       `(%93 (\%94. ((%15 ((%95 $0) (%36 %90))) ((%95 $0) (%36 ((%91 %89)
       %90))))))`)
  val slst_mem3 =
    DT(["DISK_THM"], [],
       `(%93 (\%94. ((%15 ((%95 $0) (%36 ((%91 %89) %90)))) ((%96 ((%95 $0)
       (%36 %89))) ((%95 $0) (%36 %90))))))`)
  val slst_mem4 =
    DT(["DISK_THM"], [],
       `(%52 (\%97. (%7 (\%98. (%54 (\%99. ((%15 ((%100 ((%59 ((%19 %14)
       %10)) $0)) $2)) ((%15 ((%56 %14) (%57 $0))) ((%75 ((%76 %14) $0))
       (%77 $2))))))))))`)
  val vst_append_distrib =
    DT(["DISK_THM"], [],
       `((%71 (%47 ((%101 %102) %103))) ((%5 (%47 %102)) (%47 %103)))`)
  val prop1_append_distrib =
    DT(["DISK_THM"], [],
       `(%52 (\%102. (%52 (\%103. ((%71 ((%72 %69) ((%101 $1) $0))) ((%5
       ((%72 %69) $1)) ((%72 %69) $0)))))))`)
  val prop1_r1 =
    DT(["DISK_THM"], [],
       `(%52 (\%70. ((%15 ((%72 %69) $0)) (%52 (\%97. (%104 (\%105. (%104
       (\%106. ((%15 ((%107 $3) ((%101 ((%101 $1) $2)) $0))) ((%72 %69)
       $2)))))))))))`)
  val bdt_r0 =
    DT(["DISK_THM"], [],
       `(%108 (\%109. (%110 (\%111. (%112 (\%113. ((%15 ((%114 ((%115 $2)
       $1)) (%116 $0))) (%20 ((%117 $0) %118)))))))))`)
  val bdt_r1 =
    DT(["DISK_THM"], [],
       `(%7 (\%119. (%110 (\%120. (%121 (\%122. ((%15 ((%114 ((%123 %124)
       (%125 $1))) (%116 %113))) ((%83 (%126 %113)) (%125 $1)))))))))`)
  val snd_elem =
    DT(["DISK_THM"], [],
       `(%7 (\%127. (%128 (\%129. ((%15 ((%130 $1) ((%131 %132) $0))) (%133
       (\%134. ((%135 ((%136 $0) $2)) $1))))))))`)
  val bdt_mem =
    DT(["DISK_THM"], [],
       `((%15 ((%114 ((%115 %109) %111)) (%116 %113))) ((%96 ((%83 %111)
       %25)) (%54 (\%137. ((%15 ((%138 $0) %113)) (%139 (\%140. ((%141
       ((%142 $0) $1)) %109))))))))`)
  val bdt_nil =
    DT(["DISK_THM"], [],
       `((%15 ((%114 ((%115 %109) %25)) (%116 %143))) ((%117 %143) %118))`)
  val addrule_r1 =
    DT(["DISK_THM"], [],
       `(%52 (\%144. (%145 (\%146. (%68 (\%69. ((%15 ((%147 $1) (%148 $0)))
       ((%15 ((%72 $0) $2)) ((%15 ((%149 ((%150 $2) $1)) (%151 %152)))
       ((%78 $0) %152))))))))))`)
  val sgoto_nil =
    DT(["DISK_THM"], [],
       `((%15 ((%153 (((%154 %69) ((%155 ((%156 %157) %158)) %10)) (%159
       %160))) %161)) ((%153 (((%154 %69) %10) (%159 %160))) %161))`)
  val red_eq1 =
    DT(["DISK_THM"], [],
       `((%15 (%20 ((%162 (%159 %163)) ((%164 %69) (%165 %160))))) ((%166
       (((%167 %69) %10) %163)) (((%167 %69) ((%155 ((%156 %160) ((%168
       %169) %25))) %10)) %163)))`)
  val red_eq2 =
    DT(["DISK_THM"], [],
       `((%15 ((%162 (%159 %163)) ((%164 %69) (%165 %160)))) ((%166 ((%170
       ((%171 %160) %169)) (((%167 %69) %10) %163))) (((%167 %69) ((%155
       ((%156 %160) ((%168 %169) %25))) %10)) %163)))`)
  val reduce_append =
    DT(["DISK_THM"], [],
       `((%166 (((%167 %69) ((%172 %173) %174)) %163)) ((%175 (((%167 %69)
       %173) %163)) (((%167 %69) %174) %163)))`)
  val reduce_mem =
    DT(["DISK_THM"], [],
       `(%176 (\%163. (%9 (\%10. (%177 (\%178. ((%15 ((%166 (((%167 %69)
       $1) $2)) $0)) (%145 (\%179. ((%15 ((%147 $0) $1)) (%180 (\%181.
       (%182 (\%183. ((%5 ((%184 $2) ((%171 $1) $0))) ((%185 ((%156 $1)
       ((%168 $0) %25))) $4))))))))))))))))`)
  val getstate_red =
    DT(["DISK_THM"], [],
       `(%186 (\%187. (%9 (\%10. (%13 (\%14. (%68 (\%69. ((%15 ((%188 $3)
       ((%189 (%154 $0)) (%167 $0)))) ((%15 ((%190 $0) $2)) ((%15 ((%191
       (((%192 $3) $2) $1)) (%193 %194))) ((%147 %194) (%148
       $0)))))))))))))`)
  val red_r1 =
    DT(["DISK_THM"], [],
       `((%15 ((%195 (((%196 %197) ((%198 ((%31 %14) %199)) ((%200 %70)
       ((%201 ((%19 %73) %10)) %202)))) %194)) (%203 ((%198 %204) ((%200
       %205) %206))))) (%104 (\%105. (%104 (\%106. ((%5 ((%107 %70) ((%101
       $1) $0))) (%207 (\%208. ((%107 %205) ((%101 ((%58 $0) %87))
       $1))))))))))`)
  val doReduce_vst =
    DT(["DISK_THM"], [],
       `((%15 (%47 %70)) ((%15 ((%195 (((%196 %197) ((%198 ((%31 %14)
       %199)) ((%200 %70) ((%201 ((%19 %73) %10)) %202)))) %194)) (%203
       ((%198 %204) ((%200 %205) %206))))) (%47 %205)))`)
  val list_pop =
    DT(["DISK_THM"], [],
       `(%52 (\%97. (%209 (\%210. ((%15 ((%72 %69) $1)) ((%72 %69) ((%211
       $1) $0)))))))`)
  val getstate_r1 =
    DT(["DISK_THM"], [],
       `(%186 (\%187. (%9 (\%10. (%13 (\%14. ((%15 ((%191 (((%192 $2) $1)
       $0)) (%212 ((%19 %73) %213)))) ((%15 (%33 $0)) (%33 %73)))))))))`)
  val parse_csl_not_nil =
    DT(["DISK_THM"], [],
       `(%214 (\%215. (%68 (\%69. ((%15 ((%216 $1) (%217 $0))) ((%15 ((%195
       ((%218 $1) ((%198 %219) ((%200 %70) ((%201 ((%19 %73) %10))
       %202))))) (%203 ((%198 %204) ((%200 %205) %206))))) (%20 (%220
       %206))))))))`)
  val parse_csl_validStates =
    DT(["DISK_THM"], [],
       `(%214 (\%215. (%68 (\%69. ((%15 ((%216 $1) (%217 $0))) ((%15 ((%221
       $0) ((%201 ((%19 %73) %10)) %202))) ((%15 ((%195 ((%218 $1) ((%198
       %219) ((%200 %70) ((%201 ((%19 %73) %10)) %202))))) (%203 ((%198
       %204) ((%200 %205) %206))))) ((%221 $0) %206))))))))`)
  val prop1thm =
    DT(["DISK_THM"], [],
       `(%214 (\%215. (%68 (\%69. ((%15 ((%216 $1) (%217 $0))) ((%15 ((%221
       $0) ((%201 ((%19 %73) %10)) %202))) (%52 (\%70. ((%15 ((%72 $1) $0))
       ((%15 ((%195 ((%218 $2) ((%198 %219) ((%200 $0) ((%201 ((%19 %73)
       %10)) %202))))) (%203 ((%198 %204) ((%200 %205) %206))))) ((%72 $1)
       %205)))))))))))`)
  end
  val _ = DB.bindl "parseProp1Def"
  [("stacklntmnls_primitive_def",stacklntmnls_primitive_def,DB.Def),
   ("stackltmnls_primitive_def",stackltmnls_primitive_def,DB.Def),
   ("stacklsymtree_primitive_def",stacklsymtree_primitive_def,DB.Def),
   ("validStkSymTree_primitive_def",validStkSymTree_primitive_def,DB.Def),
   ("prop1_def",prop1_def,DB.Def),
   ("stacklntmnls_ind",stacklntmnls_ind,DB.Thm),
   ("stacklntmnls_def",stacklntmnls_def,DB.Thm),
   ("stackltmnls_ind",stackltmnls_ind,DB.Thm),
   ("stackltmnls_def",stackltmnls_def,DB.Thm),
   ("stacklsymtree_ind",stacklsymtree_ind,DB.Thm),
   ("stacklsymtree_def",stacklsymtree_def,DB.Thm),
   ("validStkSymTree_ind",validStkSymTree_ind,DB.Thm),
   ("validStkSymTree_def",validStkSymTree_def,DB.Thm),
   ("slst_append",slst_append,DB.Thm), ("slst_mem1",slst_mem1,DB.Thm),
   ("slst_mem2",slst_mem2,DB.Thm), ("slst_mem3",slst_mem3,DB.Thm),
   ("slst_mem4",slst_mem4,DB.Thm),
   ("vst_append_distrib",vst_append_distrib,DB.Thm),
   ("prop1_append_distrib",prop1_append_distrib,DB.Thm),
   ("prop1_r1",prop1_r1,DB.Thm), ("bdt_r0",bdt_r0,DB.Thm),
   ("bdt_r1",bdt_r1,DB.Thm), ("snd_elem",snd_elem,DB.Thm),
   ("bdt_mem",bdt_mem,DB.Thm), ("bdt_nil",bdt_nil,DB.Thm),
   ("addrule_r1",addrule_r1,DB.Thm), ("sgoto_nil",sgoto_nil,DB.Thm),
   ("red_eq1",red_eq1,DB.Thm), ("red_eq2",red_eq2,DB.Thm),
   ("reduce_append",reduce_append,DB.Thm),
   ("reduce_mem",reduce_mem,DB.Thm), ("getstate_red",getstate_red,DB.Thm),
   ("red_r1",red_r1,DB.Thm), ("doReduce_vst",doReduce_vst,DB.Thm),
   ("list_pop",list_pop,DB.Thm), ("getstate_r1",getstate_r1,DB.Thm),
   ("parse_csl_not_nil",parse_csl_not_nil,DB.Thm),
   ("parse_csl_validStates",parse_csl_validStates,DB.Thm),
   ("prop1thm",prop1thm,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("yaccDefTheory.yaccDef_grammars",
                          yaccDefTheory.yaccDef_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "stacklntmnls")
        {Name = "stacklntmnls", Thy = "parseProp1Def"}
  val _ = update_grms
       (temp_overload_on_by_nametype "stackltmnls")
        {Name = "stackltmnls", Thy = "parseProp1Def"}
  val _ = update_grms
       (temp_overload_on_by_nametype "stacklsymtree")
        {Name = "stacklsymtree", Thy = "parseProp1Def"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validStkSymTree")
        {Name = "validStkSymTree", Thy = "parseProp1Def"}
  val _ = update_grms
       (temp_overload_on_by_nametype "prop1")
        {Name = "prop1", Thy = "parseProp1Def"}
  val parseProp1Def_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [stacklntmnls_def];  
  
  val _ = computeLib.add_funs [stackltmnls_def];  
  
  val _ = computeLib.add_funs [stacklsymtree_def];  
  
  val _ = computeLib.add_funs [validStkSymTree_def];  
  
  val _ = computeLib.add_funs [prop1_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
