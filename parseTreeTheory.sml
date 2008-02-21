structure parseTreeTheory :> parseTreeTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading parseTreeTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open grammarDefTheory
  in end;
  val _ = Theory.link_parents
          ("parseTree",
          Arbnum.fromString "1203551154",
          Arbnum.fromString "487819")
          [("grammarDef",
           Arbnum.fromString "1203551063",
           Arbnum.fromString "68399")];
  val _ = Theory.incorporate_types "parseTree"
       [("nonTerminal",0), ("listparseTree2",0), ("ptree",0),
        ("terminal",0)];
  val _ = Theory.incorporate_consts "parseTree"
     [("validptree_defn_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] -->
         bool))),
      ("dest_nonTerminal",
       ((T"nonTerminal" "parseTree" [] -->
         T"recspace" "ind_type" [T"string" "string" []]))),
      ("mk_listparseTree2",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]
         --> T"listparseTree2" "parseTree" []))),
      ("ptree1_size",
       ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" []))),
      ("ptree_case",
       (((T"terminal" "parseTree" [] --> alpha) -->
         ((T"nonTerminal" "parseTree" [] -->
           (T"list" "list" [T"ptree" "parseTree" []] --> alpha)) -->
          (T"ptree" "parseTree" [] --> alpha))))),
      ("mk_terminal",
       ((T"recspace" "ind_type" [T"string" "string" []] -->
         T"terminal" "parseTree" []))),
      ("ptreeNodeSym",
       ((T"ptree" "parseTree" [] --> T"symbol" "regexp" []))),
      ("terminal_case",
       (((T"string" "string" [] --> alpha) -->
         (T"terminal" "parseTree" [] --> alpha)))),
      ("ptreeToRules2",
       ((T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"rule" "grammarDef" []]))),
      ("parseTree7",
       ((T"nonTerminal" "parseTree" [] -->
         (T"list" "list" [T"ptree" "parseTree" []] -->
          T"ptree" "parseTree" [])))),
      ("parseTree6",
       ((T"ptree" "parseTree" [] -->
         (T"listparseTree2" "parseTree" [] -->
          T"listparseTree2" "parseTree" [])))),
      ("parseTree5",(T"listparseTree2" "parseTree" [])),
      ("parseTree4",
       ((T"nonTerminal" "parseTree" [] -->
         (T"listparseTree2" "parseTree" [] --> T"ptree" "parseTree" [])))),
      ("parseTree3",
       ((T"terminal" "parseTree" [] --> T"ptree" "parseTree" []))),
      ("parseTree1",
       ((T"string" "string" [] --> T"terminal" "parseTree" []))),
      ("parseTree0",
       ((T"string" "string" [] --> T"nonTerminal" "parseTree" []))),
      ("Node",
       ((T"nonTerminal" "parseTree" [] -->
         (T"list" "list" [T"ptree" "parseTree" []] -->
          T"ptree" "parseTree" [])))),
      ("nonTmnlToStr",
       ((T"nonTerminal" "parseTree" [] --> T"string" "string" []))),
      ("leaves",
       ((T"ptree" "parseTree" [] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("nonTerminal_case",
       (((T"string" "string" [] --> alpha) -->
         (T"nonTerminal" "parseTree" [] --> alpha)))),
      ("mk_ptree",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]
         --> T"ptree" "parseTree" []))),
      ("ptreeSubtree",
       ((T"ptree" "parseTree" [] -->
         T"list" "list" [T"ptree" "parseTree" []]))),
      ("Leaf",((T"terminal" "parseTree" [] --> T"ptree" "parseTree" []))),
      ("getSymbols",
       ((T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("ptree_size",((T"ptree" "parseTree" [] --> T"num" "num" []))),
      ("ptree2Sym",((T"ptree" "parseTree" [] --> T"symbol" "regexp" []))),
      ("cleaves",
       ((T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("ptreeToRules",
       ((T"ptree" "parseTree" [] -->
         T"list" "list" [T"rule" "grammarDef" []]))),
      ("dest_listparseTree2",
       ((T"listparseTree2" "parseTree" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"terminal" "parseTree" [],
             T"nonTerminal" "parseTree" []]]))),
      ("tmnlToStr",
       ((T"terminal" "parseTree" [] --> T"string" "string" []))),
      ("terminal_size",((T"terminal" "parseTree" [] --> T"num" "num" []))),
      ("ptheight",((T"ptree" "parseTree" [] --> T"num" "num" []))),
      ("ptheightl",
       ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" []))),
      ("mk_nonTerminal",
       ((T"recspace" "ind_type" [T"string" "string" []] -->
         T"nonTerminal" "parseTree" []))),
      ("ptreeSubtSyms",
       ((T"ptree" "parseTree" [] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("ptsizel",
       ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" []))),
      ("TM",((T"string" "string" [] --> T"terminal" "parseTree" []))),
      ("NT",((T"string" "string" [] --> T"nonTerminal" "parseTree" []))),
      ("isNode",((T"ptree" "parseTree" [] --> bool))),
      ("nonTerminal_size",
       ((T"nonTerminal" "parseTree" [] --> T"num" "num" []))),
      ("dest_ptree",
       ((T"ptree" "parseTree" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"terminal" "parseTree" [],
             T"nonTerminal" "parseTree" []]]))),
      ("validptree",
       ((T"grammar" "grammarDef" [] -->
         (T"ptree" "parseTree" [] --> bool)))),
      ("dest_terminal",
       ((T"terminal" "parseTree" [] -->
         T"recspace" "ind_type" [T"string" "string" []]))),
      ("ptsize",((T"ptree" "parseTree" [] --> T"num" "num" []))),
      ("checkRules",
       ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool)))),
      ("isLeaf",((T"ptree" "parseTree" [] --> bool)))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"nonTerminal" "parseTree" [] -->
        T"recspace" "ind_type" [T"string" "string" []]) --> bool) -->
      bool)),
   V"rep"
    ((T"nonTerminal" "parseTree" [] -->
      T"recspace" "ind_type" [T"string" "string" []])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"string" "string" []] --> bool) -->
      ((T"nonTerminal" "parseTree" [] -->
        T"recspace" "ind_type" [T"string" "string" []]) --> bool))),
   V"a0" (T"recspace" "ind_type" [T"string" "string" []]),
   C"!" "bool"
    ((((T"recspace" "ind_type" [T"string" "string" []] --> bool) --> bool)
      --> bool)),
   V"'nonTerminal'"
    ((T"recspace" "ind_type" [T"string" "string" []] --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type" [T"string" "string" []] --> bool) --> bool)),
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
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"nonTerminal" "parseTree" [] --> bool) --> bool)),
   V"a" (T"nonTerminal" "parseTree" []),
   C"=" "min"
    ((T"nonTerminal" "parseTree" [] -->
      (T"nonTerminal" "parseTree" [] --> bool))),
   C"mk_nonTerminal" "parseTree"
    ((T"recspace" "ind_type" [T"string" "string" []] -->
      T"nonTerminal" "parseTree" [])),
   C"dest_nonTerminal" "parseTree"
    ((T"nonTerminal" "parseTree" [] -->
      T"recspace" "ind_type" [T"string" "string" []])),
   V"r" (T"recspace" "ind_type" [T"string" "string" []]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min"
    (((T"string" "string" [] --> T"nonTerminal" "parseTree" []) -->
      ((T"string" "string" [] --> T"nonTerminal" "parseTree" []) -->
       bool))),
   C"parseTree0" "parseTree"
    ((T"string" "string" [] --> T"nonTerminal" "parseTree" [])),
   C"NT" "parseTree"
    ((T"string" "string" [] --> T"nonTerminal" "parseTree" [])),
   C"!" "bool" ((((T"string" "string" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"string" "string" [] --> alpha)),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"nonTerminal_case" "parseTree"
    (((T"string" "string" [] --> alpha) -->
      (T"nonTerminal" "parseTree" [] --> alpha))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"nonTerminal_size" "parseTree"
    ((T"nonTerminal" "parseTree" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"string_size" "string" ((T"string" "string" [] --> T"num" "num" [])),
   C"?" "bool"
    ((((T"terminal" "parseTree" [] -->
        T"recspace" "ind_type" [T"string" "string" []]) --> bool) -->
      bool)),
   V"rep"
    ((T"terminal" "parseTree" [] -->
      T"recspace" "ind_type" [T"string" "string" []])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type" [T"string" "string" []] --> bool) -->
      ((T"terminal" "parseTree" [] -->
        T"recspace" "ind_type" [T"string" "string" []]) --> bool))),
   V"'terminal'"
    ((T"recspace" "ind_type" [T"string" "string" []] --> bool)),
   C"!" "bool" (((T"terminal" "parseTree" [] --> bool) --> bool)),
   V"a" (T"terminal" "parseTree" []),
   C"=" "min"
    ((T"terminal" "parseTree" [] -->
      (T"terminal" "parseTree" [] --> bool))),
   C"mk_terminal" "parseTree"
    ((T"recspace" "ind_type" [T"string" "string" []] -->
      T"terminal" "parseTree" [])),
   C"dest_terminal" "parseTree"
    ((T"terminal" "parseTree" [] -->
      T"recspace" "ind_type" [T"string" "string" []])),
   C"=" "min"
    (((T"string" "string" [] --> T"terminal" "parseTree" []) -->
      ((T"string" "string" [] --> T"terminal" "parseTree" []) --> bool))),
   C"parseTree1" "parseTree"
    ((T"string" "string" [] --> T"terminal" "parseTree" [])),
   C"TM" "parseTree"
    ((T"string" "string" [] --> T"terminal" "parseTree" [])),
   C"terminal_case" "parseTree"
    (((T"string" "string" [] --> alpha) -->
      (T"terminal" "parseTree" [] --> alpha))),
   C"terminal_size" "parseTree"
    ((T"terminal" "parseTree" [] --> T"num" "num" [])),
   V"s" (T"string" "string" []),
   C"=" "min"
    ((T"string" "string" [] --> (T"string" "string" [] --> bool))),
   C"tmnlToStr" "parseTree"
    ((T"terminal" "parseTree" [] --> T"string" "string" [])),
   C"nonTmnlToStr" "parseTree"
    ((T"nonTerminal" "parseTree" [] --> T"string" "string" [])),
   C"?" "bool"
    ((((T"ptree" "parseTree" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])
       --> bool) --> bool)),
   V"rep"
    ((T"ptree" "parseTree" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
       bool) -->
      ((T"ptree" "parseTree" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])
       --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
        bool) --> bool) --> bool)),
   V"'ptree'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
      bool)),
   V"'listparseTree2'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
      bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
       bool) --> bool)), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"terminal" "parseTree" [] --> bool) --> bool)),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
       bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])
        -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [],
            T"nonTerminal" "parseTree" []]])))),
   C"," "pair"
    ((T"terminal" "parseTree" [] -->
      (T"nonTerminal" "parseTree" [] -->
       T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]))),
   C"@" "min"
    (((T"nonTerminal" "parseTree" [] --> bool) -->
      T"nonTerminal" "parseTree" [])),
   V"v" (T"nonTerminal" "parseTree" []), C"T" "bool" (bool),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]),
   C"?" "bool" (((T"nonTerminal" "parseTree" [] --> bool) --> bool)),
   V"a0" (T"nonTerminal" "parseTree" []),
   C"?" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
       bool) --> bool)),
   V"a1"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"@" "min"
    (((T"terminal" "parseTree" [] --> bool) -->
      T"terminal" "parseTree" [])), V"v" (T"terminal" "parseTree" []),
   C"FCONS" "ind_type"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
      ((T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])
       -->
       (T"num" "num" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [],
            T"nonTerminal" "parseTree" []]])))),
   V"a1'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]),
   C"!" "bool" (((T"ptree" "parseTree" [] --> bool) --> bool)),
   V"a" (T"ptree" "parseTree" []),
   C"=" "min"
    ((T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool))),
   C"mk_ptree" "parseTree"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
      T"ptree" "parseTree" [])),
   C"dest_ptree" "parseTree"
    ((T"ptree" "parseTree" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]]),
   C"?" "bool"
    ((((T"listparseTree2" "parseTree" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])
       --> bool) --> bool)),
   V"rep"
    ((T"listparseTree2" "parseTree" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
       bool) -->
      ((T"listparseTree2" "parseTree" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])
       --> bool))),
   C"!" "bool" (((T"listparseTree2" "parseTree" [] --> bool) --> bool)),
   V"a" (T"listparseTree2" "parseTree" []),
   C"=" "min"
    ((T"listparseTree2" "parseTree" [] -->
      (T"listparseTree2" "parseTree" [] --> bool))),
   C"mk_listparseTree2" "parseTree"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]] -->
      T"listparseTree2" "parseTree" [])),
   C"dest_listparseTree2" "parseTree"
    ((T"listparseTree2" "parseTree" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"terminal" "parseTree" [], T"nonTerminal" "parseTree" []]])),
   C"=" "min"
    (((T"terminal" "parseTree" [] --> T"ptree" "parseTree" []) -->
      ((T"terminal" "parseTree" [] --> T"ptree" "parseTree" []) -->
       bool))),
   C"parseTree3" "parseTree"
    ((T"terminal" "parseTree" [] --> T"ptree" "parseTree" [])),
   C"=" "min"
    (((T"nonTerminal" "parseTree" [] -->
       (T"listparseTree2" "parseTree" [] --> T"ptree" "parseTree" [])) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"listparseTree2" "parseTree" [] --> T"ptree" "parseTree" [])) -->
       bool))),
   C"parseTree4" "parseTree"
    ((T"nonTerminal" "parseTree" [] -->
      (T"listparseTree2" "parseTree" [] --> T"ptree" "parseTree" []))),
   V"a1" (T"listparseTree2" "parseTree" []),
   C"parseTree5" "parseTree" (T"listparseTree2" "parseTree" []),
   C"=" "min"
    (((T"ptree" "parseTree" [] -->
       (T"listparseTree2" "parseTree" [] -->
        T"listparseTree2" "parseTree" [])) -->
      ((T"ptree" "parseTree" [] -->
        (T"listparseTree2" "parseTree" [] -->
         T"listparseTree2" "parseTree" [])) --> bool))),
   C"parseTree6" "parseTree"
    ((T"ptree" "parseTree" [] -->
      (T"listparseTree2" "parseTree" [] -->
       T"listparseTree2" "parseTree" []))),
   V"a0" (T"ptree" "parseTree" []),
   C"=" "min"
    (((T"nonTerminal" "parseTree" [] -->
       (T"list" "list" [T"ptree" "parseTree" []] -->
        T"ptree" "parseTree" [])) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         T"ptree" "parseTree" [])) --> bool))),
   C"parseTree7" "parseTree"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []))),
   V"a1" (T"list" "list" [T"ptree" "parseTree" []]),
   C"@" "min"
    ((((T"list" "list" [T"ptree" "parseTree" []] -->
        T"listparseTree2" "parseTree" []) --> bool) -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"listparseTree2" "parseTree" []))),
   V"fn"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"listparseTree2" "parseTree" [])),
   C"NIL" "list" (T"list" "list" [T"ptree" "parseTree" []]),
   C"!" "bool"
    (((T"list" "list" [T"ptree" "parseTree" []] --> bool) --> bool)),
   C"CONS" "list"
    ((T"ptree" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"Leaf" "parseTree"
    ((T"terminal" "parseTree" [] --> T"ptree" "parseTree" [])),
   C"Node" "parseTree"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []))),
   C"!" "bool"
    ((((T"terminal" "parseTree" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"terminal" "parseTree" [] --> alpha)),
   C"!" "bool"
    ((((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] --> alpha)) --> bool) -->
      bool)),
   V"f1"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> alpha))),
   C"ptree_case" "parseTree"
    (((T"terminal" "parseTree" [] --> alpha) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] --> alpha)) -->
       (T"ptree" "parseTree" [] --> alpha)))),
   C"ptree_size" "parseTree"
    ((T"ptree" "parseTree" [] --> T"num" "num" [])),
   C"ptree1_size" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" [])),
   V"nt" (T"nonTerminal" "parseTree" []),
   V"ptl" (T"list" "list" [T"ptree" "parseTree" []]),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"ptree2Sym" "parseTree"
    ((T"ptree" "parseTree" [] --> T"symbol" "regexp" [])),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   V"tm" (T"terminal" "parseTree" []),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   V"v0" (T"nonTerminal" "parseTree" []),
   V"v1" (T"list" "list" [T"ptree" "parseTree" []]),
   C"isNode" "parseTree" ((T"ptree" "parseTree" [] --> bool)),
   V"v2" (T"terminal" "parseTree" []), C"F" "bool" (bool),
   C"isLeaf" "parseTree" ((T"ptree" "parseTree" [] --> bool)),
   V"tmnl" (T"terminal" "parseTree" []),
   C"ptsize" "parseTree" ((T"ptree" "parseTree" [] --> T"num" "num" [])),
   V"ptlist" (T"list" "list" [T"ptree" "parseTree" []]),
   C"ptsizel" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" [])),
   V"h" (T"ptree" "parseTree" []),
   V"t" (T"list" "list" [T"ptree" "parseTree" []]),
   C"ptheight" "parseTree" ((T"ptree" "parseTree" [] --> T"num" "num" [])),
   C"ptheightl" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" [])),
   C"=" "min"
    (((T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"symbol" "regexp" []]) -->
      ((T"list" "list" [T"ptree" "parseTree" []] -->
        T"list" "list" [T"symbol" "regexp" []]) --> bool))),
   C"getSymbols" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"WFREC" "relation"
    (((T"list" "list" [T"ptree" "parseTree" []] -->
       (T"list" "list" [T"ptree" "parseTree" []] --> bool)) -->
      (((T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"symbol" "regexp" []]) -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"ptree" "parseTree" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"@" "min"
    ((((T"list" "list" [T"ptree" "parseTree" []] -->
        (T"list" "list" [T"ptree" "parseTree" []] --> bool)) --> bool) -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       (T"list" "list" [T"ptree" "parseTree" []] --> bool)))),
   V"R"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> bool))),
   C"WF" "relation"
    (((T"list" "list" [T"ptree" "parseTree" []] -->
       (T"list" "list" [T"ptree" "parseTree" []] --> bool)) --> bool)),
   V"v6" (T"list" "list" [T"ptree" "parseTree" []]),
   V"v5" (T"ptree" "parseTree" []),
   V"v10" (T"list" "list" [T"ptree" "parseTree" []]),
   V"v9" (T"ptree" "parseTree" []),
   V"getSymbols"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   V"a" (T"list" "list" [T"ptree" "parseTree" []]),
   C"list_case" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      ((T"ptree" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"ptree" "parseTree" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"I" "combin"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   V"v" (T"ptree" "parseTree" []),
   C"ptree_case" "parseTree"
    (((T"terminal" "parseTree" [] -->
       T"list" "list" [T"symbol" "regexp" []]) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"ptree" "parseTree" [] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"v7" (T"ptree" "parseTree" []),
   V"v8" (T"list" "list" [T"ptree" "parseTree" []]),
   V"v11" (T"ptree" "parseTree" []),
   V"v12" (T"list" "list" [T"ptree" "parseTree" []]),
   C"=" "min"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"ptreeToRules" "parseTree"
    ((T"ptree" "parseTree" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"NIL" "list" (T"list" "list" [T"rule" "grammarDef" []]),
   C"CONS" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   C"ptreeToRules2" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"APPEND" "list"
    ((T"list" "list" [T"rule" "grammarDef" []] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"rule" "grammarDef" []]))),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"rls" (T"list" "list" [alpha]),
   C"checkRules" "parseTree"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"NIL" "list" (T"list" "list" [alpha]),
   C"!" "bool" (((alpha --> bool) --> bool)), V"h" (alpha),
   V"t" (T"list" "list" [alpha]),
   C"CONS" "list"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool))),
   C"=" "min"
    (((T"ptree" "parseTree" [] --> T"symbol" "regexp" []) -->
      ((T"ptree" "parseTree" [] --> T"symbol" "regexp" []) --> bool))),
   C"ptreeNodeSym" "parseTree"
    ((T"ptree" "parseTree" [] --> T"symbol" "regexp" [])),
   C"WFREC" "relation"
    (((T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool)) -->
      (((T"ptree" "parseTree" [] --> T"symbol" "regexp" []) -->
        (T"ptree" "parseTree" [] --> T"symbol" "regexp" [])) -->
       (T"ptree" "parseTree" [] --> T"symbol" "regexp" [])))),
   C"@" "min"
    ((((T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool)) -->
       bool) -->
      (T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool)))),
   V"R" ((T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool))),
   C"WF" "relation"
    (((T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool)) -->
      bool)),
   V"ptreeNodeSym" ((T"ptree" "parseTree" [] --> T"symbol" "regexp" [])),
   C"ptree_case" "parseTree"
    (((T"terminal" "parseTree" [] --> T"symbol" "regexp" []) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         T"symbol" "regexp" [])) -->
       (T"ptree" "parseTree" [] --> T"symbol" "regexp" [])))),
   C"terminal_case" "parseTree"
    (((T"string" "string" [] --> T"symbol" "regexp" []) -->
      (T"terminal" "parseTree" [] --> T"symbol" "regexp" []))),
   V"tm" (T"string" "string" []),
   C"I" "combin" ((T"symbol" "regexp" [] --> T"symbol" "regexp" [])),
   V"v1" (T"nonTerminal" "parseTree" []),
   V"tl" (T"list" "list" [T"ptree" "parseTree" []]),
   C"nonTerminal_case" "parseTree"
    (((T"string" "string" [] --> T"symbol" "regexp" []) -->
      (T"nonTerminal" "parseTree" [] --> T"symbol" "regexp" []))),
   V"nt" (T"string" "string" []),
   C"=" "min"
    (((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      ((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])
       --> bool))),
   C"ptreeSubtSyms" "parseTree"
    ((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"WFREC" "relation"
    (((T"ptree" "parseTree" [] --> (T"ptree" "parseTree" [] --> bool)) -->
      (((T"ptree" "parseTree" [] -->
         T"list" "list" [T"symbol" "regexp" []]) -->
        (T"ptree" "parseTree" [] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"ptree" "parseTree" [] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   V"ptreeSubtSyms"
    ((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"terminal_case" "parseTree"
    (((T"string" "string" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      (T"terminal" "parseTree" [] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"nonTerminal_case" "parseTree"
    (((T"string" "string" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      (T"nonTerminal" "parseTree" [] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"MAP" "list"
    (((T"ptree" "parseTree" [] --> T"symbol" "regexp" []) -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"x" (T"nonTerminal" "parseTree" []),
   V"l" (T"list" "list" [T"ptree" "parseTree" []]),
   C"=" "min"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> bool))),
   C"ptreeSubtree" "parseTree"
    ((T"ptree" "parseTree" [] -->
      T"list" "list" [T"ptree" "parseTree" []])),
   C"=" "min"
    (((T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
       --> bool) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] --> bool)
       --> bool))),
   C"validptree_defn_tupled" "parseTree"
    ((T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
      --> bool)),
   C"WFREC" "relation"
    (((T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] --> bool))
      -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] --> bool)
        -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] --> bool))
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] -->
        bool)))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] --> bool))
       --> bool) -->
      (T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] -->
        bool)))),
   V"R"
    ((T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
      -->
      (T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
       --> bool))),
   C"WF" "relation"
    (((T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
       -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [], T"ptree" "parseTree" []] --> bool))
      --> bool)),
   C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"g" (T"grammar" "grammarDef" []), V"n" (T"nonTerminal" "parseTree" []),
   V"e" (T"ptree" "parseTree" []),
   C"MEM" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"rules" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"MEM" "list"
    ((T"ptree" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> bool))),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"ptree" "parseTree" [] -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]))),
   V"validptree_defn_tupled"
    ((T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
      --> bool)),
   V"a"
    (T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] --> (T"ptree" "parseTree" [] --> bool))
      -->
      (T"prod" "pair" [T"grammar" "grammarDef" [], T"ptree" "parseTree" []]
       --> bool))), V"v1" (T"ptree" "parseTree" []),
   C"ptree_case" "parseTree"
    (((T"terminal" "parseTree" [] --> bool) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] --> bool)) -->
       (T"ptree" "parseTree" [] --> bool)))),
   C"I" "combin" ((bool --> bool)), V"x" (T"grammar" "grammarDef" []),
   V"x1" (T"ptree" "parseTree" []),
   C"validptree" "parseTree"
    ((T"grammar" "grammarDef" [] --> (T"ptree" "parseTree" [] --> bool))),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"leaves" "parseTree"
    ((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"cleaves" "parseTree"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"APPEND" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"nonTerminal"
    (((T"string" "string" [] --> T"nonTerminal" "parseTree" []) --> bool)),
   V"a'" (T"string" "string" []), V"M" (T"nonTerminal" "parseTree" []),
   V"M'" (T"nonTerminal" "parseTree" []),
   V"f'" ((T"string" "string" [] --> alpha)),
   C"?" "bool"
    ((((T"nonTerminal" "parseTree" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"nonTerminal" "parseTree" [] --> alpha)),
   C"!" "bool"
    ((((T"nonTerminal" "parseTree" [] --> bool) --> bool) --> bool)),
   V"P" ((T"nonTerminal" "parseTree" [] --> bool)),
   V"terminal"
    (((T"string" "string" [] --> T"terminal" "parseTree" []) --> bool)),
   V"M" (T"terminal" "parseTree" []), V"M'" (T"terminal" "parseTree" []),
   V"t" (T"terminal" "parseTree" []),
   C"?" "bool"
    ((((T"terminal" "parseTree" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"terminal" "parseTree" [] --> alpha)),
   C"!" "bool"
    ((((T"terminal" "parseTree" [] --> bool) --> bool) --> bool)),
   V"P" ((T"terminal" "parseTree" [] --> bool)),
   V"ptree"
    (((T"terminal" "parseTree" [] --> T"ptree" "parseTree" []) -->
      ((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         T"ptree" "parseTree" [])) --> bool))),
   V"a'" (T"terminal" "parseTree" []),
   V"a0'" (T"nonTerminal" "parseTree" []),
   V"a1'" (T"list" "list" [T"ptree" "parseTree" []]),
   C"~" "bool" ((bool --> bool)), V"M" (T"ptree" "parseTree" []),
   V"M'" (T"ptree" "parseTree" []),
   V"f'" ((T"terminal" "parseTree" [] --> alpha)),
   V"f1'"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> alpha))),
   V"p" (T"ptree" "parseTree" []),
   C"?" "bool"
    (((T"list" "list" [T"ptree" "parseTree" []] --> bool) --> bool)),
   V"f0" ((T"terminal" "parseTree" [] --> alpha)),
   C"!" "bool"
    ((((T"nonTerminal" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] --> (beta --> alpha)))
       --> bool) --> bool)),
   V"f1"
    ((T"nonTerminal" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] --> (beta --> alpha)))),
   C"!" "bool" (((beta --> bool) --> bool)), V"f2" (beta),
   C"!" "bool"
    ((((T"ptree" "parseTree" [] -->
        (T"list" "list" [T"ptree" "parseTree" []] -->
         (alpha --> (beta --> beta)))) --> bool) --> bool)),
   V"f3"
    ((T"ptree" "parseTree" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       (alpha --> (beta --> beta))))),
   C"?" "bool" ((((T"ptree" "parseTree" [] --> alpha) --> bool) --> bool)),
   V"fn0" ((T"ptree" "parseTree" [] --> alpha)),
   C"?" "bool"
    ((((T"list" "list" [T"ptree" "parseTree" []] --> beta) --> bool) -->
      bool)), V"fn1" ((T"list" "list" [T"ptree" "parseTree" []] --> beta)),
   C"=" "min" ((beta --> (beta --> bool))),
   C"!" "bool" ((((T"ptree" "parseTree" [] --> bool) --> bool) --> bool)),
   V"P0" ((T"ptree" "parseTree" [] --> bool)),
   C"!" "bool"
    ((((T"list" "list" [T"ptree" "parseTree" []] --> bool) --> bool) -->
      bool)), V"P1" ((T"list" "list" [T"ptree" "parseTree" []] --> bool)),
   C"APPEND" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   V"l1" (T"list" "list" [T"ptree" "parseTree" []]),
   V"l2" (T"list" "list" [T"ptree" "parseTree" []]),
   V"P" ((T"list" "list" [T"ptree" "parseTree" []] --> bool)),
   V"v" (T"list" "list" [T"ptree" "parseTree" []]),
   V"P" ((T"ptree" "parseTree" [] --> bool)),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] --> (T"ptree" "parseTree" [] --> bool))
       --> bool) --> bool)),
   V"P"
    ((T"grammar" "grammarDef" [] --> (T"ptree" "parseTree" [] --> bool))),
   V"v" (T"grammar" "grammarDef" []),
   C"FLAT" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"MAP" "list"
    (((T"ptree" "parseTree" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
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
   C"SND" "pair"
    ((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
      T"ptree" "parseTree" [])),
   V"p" (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C"MAP" "list"
    (((T"prod" "pair" [alpha, T"ptree" "parseTree" []] -->
       T"ptree" "parseTree" []) -->
      (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"LENGTH" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] --> T"num" "num" [])),
   C"LENGTH" "list"
    ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" [])),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   C">=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"take1" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"take1" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"list" "list" [T"ptree" "parseTree" []]))),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]] -->
       bool) --> bool)),
   V"l" (T"list" "list" [T"prod" "pair" [alpha, T"ptree" "parseTree" []]]),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
      (T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
       bool))),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"ptree" "parseTree" []] -->
       T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]]))),
   C"SOME" "option"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]])),
   V"x" (T"list" "list" [T"ptree" "parseTree" []]),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"option" "option" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [T"ptree" "parseTree" []]] -->
      T"list" "list" [T"ptree" "parseTree" []])),
   C"APPEND" "list"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   V"l1" (T"list" "list" [alpha]), V"l2" (T"list" "list" [alpha]),
   V"rs" (T"list" "list" [alpha]),
   C"REVERSE" "list"
    ((T"list" "list" [T"ptree" "parseTree" []] -->
      T"list" "list" [T"ptree" "parseTree" []])),
   C"REVERSE" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []]))]
  val DT = Thm.disk_thm share_table
  in
  val nonTerminal_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 (%8 (\%9. ((%10
       $1) ((\%9. (((%11 %12) $0) (\%13. %14))) $0))))) ($1 $0))))) ($0
       $1)))))) $0)))`)
  val nonTerminal_repfns =
    DT(["DISK_THM"], [],
       `((%15 (%16 (\%17. ((%18 (%19 (%20 $0))) $0)))) (%7 (\%21. ((%22
       ((\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 (%8 (\%9. ((%10 $1) ((\%9.
       (((%11 %12) $0) (\%13. %14))) $0))))) ($1 $0))))) ($0 $1))))) $0))
       ((%10 (%20 (%19 $0))) $0)))))`)
  val parseTree0_def =
    DT([], [],
       `((%23 %24) (\%9. (%19 ((\%9. (((%11 %12) $0) (\%13. %14))) $0))))`)
  val NT = DT([], [], `((%23 %25) %24)`)
  val nonTerminal_case_def =
    DT(["DISK_THM"], [],
       `(%26 (\%27. (%28 (\%9. ((%29 ((%30 $1) (%25 $0))) ($1 $0))))))`)
  val nonTerminal_size_def =
    DT(["DISK_THM"], [],
       `(%28 (\%9. ((%31 (%32 (%25 $0))) ((%33 (%34 (%35 %36))) (%37
       $0)))))`)
  val terminal_TY_DEF =
    DT(["DISK_THM"], [],
       `(%38 (\%39. ((%40 (\%3. (%4 (\%41. ((%6 (%7 (\%3. ((%6 (%8 (\%9.
       ((%10 $1) ((\%9. (((%11 %12) $0) (\%13. %14))) $0))))) ($1 $0)))))
       ($0 $1)))))) $0)))`)
  val terminal_repfns =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%43. ((%44 (%45 (%46 $0))) $0)))) (%7 (\%21. ((%22
       ((\%3. (%4 (\%41. ((%6 (%7 (\%3. ((%6 (%8 (\%9. ((%10 $1) ((\%9.
       (((%11 %12) $0) (\%13. %14))) $0))))) ($1 $0))))) ($0 $1))))) $0))
       ((%10 (%46 (%45 $0))) $0)))))`)
  val parseTree1_def =
    DT([], [],
       `((%47 %48) (\%9. (%45 ((\%9. (((%11 %12) $0) (\%13. %14))) $0))))`)
  val TM = DT([], [], `((%47 %49) %48)`)
  val terminal_case_def =
    DT(["DISK_THM"], [],
       `(%26 (\%27. (%28 (\%9. ((%29 ((%50 $1) (%49 $0))) ($1 $0))))))`)
  val terminal_size_def =
    DT(["DISK_THM"], [],
       `(%28 (\%9. ((%31 (%51 (%49 $0))) ((%33 (%34 (%35 %36))) (%37
       $0)))))`)
  val tmnlToStr_def =
    DT(["DISK_THM"], [], `(%28 (\%52. ((%53 (%54 (%49 $0))) $0)))`)
  val nonTmnlToStr_def =
    DT(["DISK_THM"], [], `(%28 (\%52. ((%53 (%55 (%25 $0))) $0)))`)
  val ptree_TY_DEF =
    DT(["DISK_THM"], [],
       `(%56 (\%57. ((%58 (\%59. (%60 (\%61. (%60 (\%62. ((%6 ((%15 (%63
       (\%59. ((%6 ((%64 (%65 (\%43. ((%66 $1) ((\%43. (((%67 %12) ((%68
       $0) (%69 (\%70. %71)))) (\%13. %72))) $0))))) (%73 (\%74. (%75
       (\%76. ((%15 ((%66 $2) (((\%74. (\%76. (((%67 (%77 %12)) ((%68 (%78
       (\%79. %71))) $1)) ((%80 $0) (\%13. %72))))) $1) $0))) ($3
       $0)))))))) ($2 $0))))) (%63 (\%81. ((%6 ((%64 ((%66 $0) (((%67 (%77
       (%77 %12))) ((%68 (%78 (\%79. %71))) (%69 (\%70. %71)))) (\%13.
       %72)))) (%75 (\%82. (%75 (\%76. ((%15 ((%66 $2) (((\%82. (\%76.
       (((%67 (%77 (%77 (%77 %12)))) ((%68 (%78 (\%79. %71))) (%69 (\%70.
       %71)))) ((%80 $1) ((%80 $0) (\%13. %72)))))) $1) $0))) ((%15 ($4
       $1)) ($3 $0))))))))) ($1 $0)))))) ($1 $2)))))))) $0)))`)
  val ptree_repfns =
    DT(["DISK_THM"], [],
       `((%15 (%83 (\%84. ((%85 (%86 (%87 $0))) $0)))) (%63 (\%88. ((%22
       ((\%59. (%60 (\%61. (%60 (\%62. ((%6 ((%15 (%63 (\%59. ((%6 ((%64
       (%65 (\%43. ((%66 $1) ((\%43. (((%67 %12) ((%68 $0) (%69 (\%70.
       %71)))) (\%13. %72))) $0))))) (%73 (\%74. (%75 (\%76. ((%15 ((%66
       $2) (((\%74. (\%76. (((%67 (%77 %12)) ((%68 (%78 (\%79. %71))) $1))
       ((%80 $0) (\%13. %72))))) $1) $0))) ($3 $0)))))))) ($2 $0))))) (%63
       (\%81. ((%6 ((%64 ((%66 $0) (((%67 (%77 (%77 %12))) ((%68 (%78
       (\%79. %71))) (%69 (\%70. %71)))) (\%13. %72)))) (%75 (\%82. (%75
       (\%76. ((%15 ((%66 $2) (((\%82. (\%76. (((%67 (%77 (%77 (%77 %12))))
       ((%68 (%78 (\%79. %71))) (%69 (\%70. %71)))) ((%80 $1) ((%80 $0)
       (\%13. %72)))))) $1) $0))) ((%15 ($4 $1)) ($3 $0))))))))) ($1
       $0)))))) ($1 $2))))))) $0)) ((%66 (%87 (%86 $0))) $0)))))`)
  val listparseTree2_TY_DEF =
    DT(["DISK_THM"], [],
       `(%89 (\%90. ((%91 (\%81. (%60 (\%61. (%60 (\%62. ((%6 ((%15 (%63
       (\%59. ((%6 ((%64 (%65 (\%43. ((%66 $1) ((\%43. (((%67 %12) ((%68
       $0) (%69 (\%70. %71)))) (\%13. %72))) $0))))) (%73 (\%74. (%75
       (\%76. ((%15 ((%66 $2) (((\%74. (\%76. (((%67 (%77 %12)) ((%68 (%78
       (\%79. %71))) $1)) ((%80 $0) (\%13. %72))))) $1) $0))) ($3
       $0)))))))) ($2 $0))))) (%63 (\%81. ((%6 ((%64 ((%66 $0) (((%67 (%77
       (%77 %12))) ((%68 (%78 (\%79. %71))) (%69 (\%70. %71)))) (\%13.
       %72)))) (%75 (\%82. (%75 (\%76. ((%15 ((%66 $2) (((\%82. (\%76.
       (((%67 (%77 (%77 (%77 %12)))) ((%68 (%78 (\%79. %71))) (%69 (\%70.
       %71)))) ((%80 $1) ((%80 $0) (\%13. %72)))))) $1) $0))) ((%15 ($4
       $1)) ($3 $0))))))))) ($1 $0)))))) ($0 $2)))))))) $0)))`)
  val listparseTree2_repfns =
    DT(["DISK_THM"], [],
       `((%15 (%92 (\%93. ((%94 (%95 (%96 $0))) $0)))) (%63 (\%88. ((%22
       ((\%81. (%60 (\%61. (%60 (\%62. ((%6 ((%15 (%63 (\%59. ((%6 ((%64
       (%65 (\%43. ((%66 $1) ((\%43. (((%67 %12) ((%68 $0) (%69 (\%70.
       %71)))) (\%13. %72))) $0))))) (%73 (\%74. (%75 (\%76. ((%15 ((%66
       $2) (((\%74. (\%76. (((%67 (%77 %12)) ((%68 (%78 (\%79. %71))) $1))
       ((%80 $0) (\%13. %72))))) $1) $0))) ($3 $0)))))))) ($2 $0))))) (%63
       (\%81. ((%6 ((%64 ((%66 $0) (((%67 (%77 (%77 %12))) ((%68 (%78
       (\%79. %71))) (%69 (\%70. %71)))) (\%13. %72)))) (%75 (\%82. (%75
       (\%76. ((%15 ((%66 $2) (((\%82. (\%76. (((%67 (%77 (%77 (%77 %12))))
       ((%68 (%78 (\%79. %71))) (%69 (\%70. %71)))) ((%80 $1) ((%80 $0)
       (\%13. %72)))))) $1) $0))) ((%15 ($4 $1)) ($3 $0))))))))) ($1
       $0)))))) ($0 $2))))))) $0)) ((%66 (%96 (%95 $0))) $0)))))`)
  val parseTree3_def =
    DT([], [],
       `((%97 %98) (\%43. (%86 ((\%43. (((%67 %12) ((%68 $0) (%69 (\%70.
       %71)))) (\%13. %72))) $0))))`)
  val parseTree4_def =
    DT([], [],
       `((%99 %100) (\%74. (\%101. (%86 (((\%74. (\%76. (((%67 (%77 %12))
       ((%68 (%78 (\%79. %71))) $1)) ((%80 $0) (\%13. %72))))) $1) (%96
       $0))))))`)
  val parseTree5_def =
    DT([], [],
       `((%94 %102) (%95 (((%67 (%77 (%77 %12))) ((%68 (%78 (\%79. %71)))
       (%69 (\%70. %71)))) (\%13. %72))))`)
  val parseTree6_def =
    DT([], [],
       `((%103 %104) (\%105. (\%101. (%95 (((\%82. (\%76. (((%67 (%77 (%77
       (%77 %12)))) ((%68 (%78 (\%79. %71))) (%69 (\%70. %71)))) ((%80 $1)
       ((%80 $0) (\%13. %72)))))) (%87 $1)) (%96 $0))))))`)
  val parseTree7 =
    DT([], [],
       `((%106 %107) (\%74. (\%108. ((%100 $1) ((%109 (\%110. ((%15 ((%94
       ($0 %111)) %102)) (%83 (\%105. (%112 (\%108. ((%94 ($2 ((%113 $1)
       $0))) ((%104 $1) ($2 $0)))))))))) $0)))))`)
  val Leaf = DT([], [], `((%97 %114) %98)`)
  val Node = DT([], [], `((%106 %115) %107)`)
  val ptree_case_def =
    DT(["DISK_THM"], [],
       `((%15 (%116 (\%117. (%118 (\%119. (%42 (\%43. ((%29 (((%120 $2) $1)
       (%114 $0))) ($2 $0))))))))) (%116 (\%117. (%118 (\%119. (%16 (\%74.
       (%112 (\%108. ((%29 (((%120 $3) $2) ((%115 $1) $0))) (($2 $1)
       $0)))))))))))`)
  val ptree_size_def =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%43. ((%31 (%121 (%114 $0))) ((%33 (%34 (%35 %36)))
       (%51 $0)))))) ((%15 (%16 (\%74. (%112 (\%108. ((%31 (%121 ((%115 $1)
       $0))) ((%33 (%34 (%35 %36))) ((%33 (%32 $1)) (%122 $0))))))))) ((%15
       ((%31 (%122 %111)) %12)) (%83 (\%105. (%112 (\%108. ((%31 (%122
       ((%113 $1) $0))) ((%33 (%34 (%35 %36))) ((%33 (%121 $1)) (%122
       $0)))))))))))`)
  val ptree2Sym_def =
    DT(["DISK_THM"], [],
       `((%15 (%16 (\%123. (%112 (\%124. ((%125 (%126 ((%115 $1) $0)))
       (%127 (%55 $1)))))))) (%42 (\%128. ((%125 (%126 (%114 $0))) (%129
       (%54 $0))))))`)
  val isNode_def =
    DT(["DISK_THM"], [],
       `((%15 (%16 (\%130. (%112 (\%131. ((%22 (%132 ((%115 $1) $0)))
       %71)))))) (%42 (\%133. ((%22 (%132 (%114 $0))) %134))))`)
  val isLeaf_def =
    DT(["DISK_THM"], [],
       `((%15 (%16 (\%130. (%112 (\%131. ((%22 (%135 ((%115 $1) $0)))
       %134)))))) (%42 (\%133. ((%22 (%135 (%114 $0))) %71))))`)
  val ptsize_def =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%136. ((%31 (%137 (%114 $0))) (%34 (%35 %36))))))
       ((%15 (%16 (\%123. (%112 (\%138. ((%31 (%137 ((%115 $1) $0))) ((%33
       (%34 (%35 %36))) (%139 $0)))))))) ((%15 ((%31 (%139 %111)) %12))
       (%83 (\%140. (%112 (\%141. ((%31 (%139 ((%113 $1) $0))) ((%33 (%137
       $1)) (%139 $0))))))))))`)
  val ptheight_def =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%136. ((%31 (%142 (%114 $0))) %12)))) ((%15 (%16
       (\%123. (%112 (\%138. ((%31 (%142 ((%115 $1) $0))) ((%33 (%34 (%35
       %36))) (%143 $0)))))))) ((%15 ((%31 (%143 %111)) %12)) (%83 (\%140.
       (%112 (\%141. ((%31 (%143 ((%113 $1) $0))) ((%33 (%142 $1)) (%143
       $0))))))))))`)
  val getSymbols_primitive_def =
    DT([], [],
       `((%144 %145) ((%146 (%147 (\%148. ((%15 (%149 $0)) ((%15 (%42
       (\%136. (%112 (\%150. (%83 (\%151. (($3 ((%113 $0) $1)) ((%113 (%114
       $2)) ((%113 $0) $1)))))))))) (%112 (\%138. (%16 (\%123. (%112
       (\%152. (%83 (\%153. (($4 ((%113 $0) $1)) ((%113 ((%115 $2) $3))
       ((%113 $0) $1)))))))))))))))) (\%154. (\%155. (((%156 (%157 %158))
       (\%159. (\%131. (((%160 (\%136. (((%156 (%157 ((%161 (%129 (%54
       $0))) %158))) (\%162. (\%163. (%157 ((%161 (%129 (%54 $2))) ($6
       ((%113 $1) $0))))))) $1))) (\%123. (\%138. (((%156 (%157 ((%161
       (%127 (%55 $1))) %158))) (\%164. (\%165. (%157 ((%161 (%127 (%55
       $3))) ($7 ((%113 $1) $0))))))) $2)))) $1)))) $0)))))`)
  val ptreeToRules_def =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%136. ((%166 (%167 (%114 $0))) %168)))) ((%15 (%16
       (\%123. (%112 (\%138. ((%166 (%167 ((%115 $1) $0))) ((%169 ((%170
       (%55 $1)) (%145 $0))) (%171 $0)))))))) ((%15 ((%166 (%171 %111))
       %168)) (%83 (\%140. (%112 (\%141. ((%166 (%171 ((%113 $1) $0)))
       ((%172 (%167 $1)) (%171 $0))))))))))`)
  val checkRules_def =
    DT(["DISK_THM"], [],
       `((%15 (%173 (\%174. ((%22 ((%175 %176) $0)) %71)))) (%177 (\%178.
       (%173 (\%179. (%173 (\%174. ((%22 ((%175 ((%180 $2) $1)) $0)) ((%15
       ((%181 $2) $0)) ((%175 $1) $0))))))))))`)
  val ptreeNodeSym_primitive_def =
    DT([], [],
       `((%182 %183) ((%184 (%185 (\%186. (%187 $0)))) (\%188. (\%84.
       (((%189 (\%79. ((%190 (\%191. (%192 (%129 $0)))) $0))) (\%193.
       (\%194. ((%195 (\%196. (%192 (%127 $0)))) $1)))) $0)))))`)
  val ptreeSubtSyms_primitive_def =
    DT([], [],
       `((%197 %198) ((%199 (%185 (\%186. (%187 $0)))) (\%200. (\%84.
       (((%160 (\%79. ((%201 (\%191. (%157 %158))) $0))) (\%193. (\%194.
       ((%202 (\%196. (%157 ((%203 %183) $1)))) $1)))) $0)))))`)
  val ptreeSubtree_def =
    DT(["DISK_THM"], [],
       `((%15 (%16 (\%204. (%112 (\%205. ((%206 (%207 ((%115 $1) $0)))
       $0)))))) (%42 (\%128. ((%206 (%207 (%114 $0))) %111))))`)
  val validptree_defn_tupled_primitive_def =
    DT([], [],
       `((%208 %209) ((%210 (%211 (\%212. ((%15 (%213 $0)) (%214 (\%215.
       (%112 (\%124. (%16 (\%216. (%83 (\%217. ((%6 ((%15 ((%218 ((%170
       (%55 $1)) (%145 $2))) (%219 $3))) ((%15 ((%220 $0) $2)) (%132 $0))))
       (($4 ((%221 $3) $0)) ((%221 $3) ((%115 $1) $2))))))))))))))))
       (\%222. (\%223. ((%224 (\%215. (\%225. (((%226 (\%128. (%227 %134)))
       (\%216. (\%124. (%227 ((%15 ((%218 ((%170 (%55 $1)) (%145 $0)))
       (%219 $3))) (%83 (\%217. ((%6 ((%220 $0) $1)) ((%6 (%132 $0)) ($6
       ((%221 $4) $0))))))))))) $0)))) $0)))))`)
  val validptree_defn_curried_def =
    DT([], [],
       `(%214 (\%228. (%83 (\%229. ((%22 ((%230 $1) $0)) (%209 ((%221 $1)
       $0)))))))`)
  val leaves_def =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%136. ((%231 (%232 (%114 $0))) ((%161 (%129 (%54 $0)))
       %158))))) ((%15 (%16 (\%123. (%112 (\%138. ((%231 (%232 ((%115 $1)
       $0))) (%233 $0))))))) ((%15 ((%231 (%233 %111)) %158)) (%83 (\%140.
       (%112 (\%141. ((%231 (%233 ((%113 $1) $0))) ((%234 (%232 $1)) (%233
       $0))))))))))`)
  val datatype_nonTerminal = DT(["DISK_THM"], [], `(%235 (%236 %25))`)
  val nonTerminal_11 =
    DT(["DISK_THM"], [],
       `(%28 (\%9. (%28 (\%237. ((%22 ((%18 (%25 $1)) (%25 $0))) ((%53 $1)
       $0))))))`)
  val nonTerminal_case_cong =
    DT(["DISK_THM"], [],
       `(%16 (\%238. (%16 (\%239. (%26 (\%27. ((%6 ((%15 ((%18 $2) $1))
       (%28 (\%9. ((%6 ((%18 $2) (%25 $0))) ((%29 ($1 $0)) (%240 $0)))))))
       ((%29 ((%30 $0) $2)) ((%30 %240) $1)))))))))`)
  val nonTerminal_nchotomy =
    DT(["DISK_THM"], [], `(%16 (\%216. (%8 (\%52. ((%18 $1) (%25 $0))))))`)
  val nonTerminal_Axiom =
    DT(["DISK_THM"], [],
       `(%26 (\%27. (%241 (\%242. (%28 (\%9. ((%29 ($1 (%25 $0))) ($2
       $0))))))))`)
  val nonTerminal_induction =
    DT(["DISK_THM"], [],
       `(%243 (\%244. ((%6 (%28 (\%52. ($1 (%25 $0))))) (%16 (\%216. ($1
       $0))))))`)
  val datatype_terminal = DT(["DISK_THM"], [], `(%235 (%245 %49))`)
  val terminal_11 =
    DT(["DISK_THM"], [],
       `(%28 (\%9. (%28 (\%237. ((%22 ((%44 (%49 $1)) (%49 $0))) ((%53 $1)
       $0))))))`)
  val terminal_case_cong =
    DT(["DISK_THM"], [],
       `(%42 (\%246. (%42 (\%247. (%26 (\%27. ((%6 ((%15 ((%44 $2) $1))
       (%28 (\%9. ((%6 ((%44 $2) (%49 $0))) ((%29 ($1 $0)) (%240 $0)))))))
       ((%29 ((%50 $0) $2)) ((%50 %240) $1)))))))))`)
  val terminal_nchotomy =
    DT(["DISK_THM"], [], `(%42 (\%248. (%8 (\%52. ((%44 $1) (%49 $0))))))`)
  val terminal_Axiom =
    DT(["DISK_THM"], [],
       `(%26 (\%27. (%249 (\%250. (%28 (\%9. ((%29 ($1 (%49 $0))) ($2
       $0))))))))`)
  val terminal_induction =
    DT(["DISK_THM"], [],
       `(%251 (\%252. ((%6 (%28 (\%52. ($1 (%49 $0))))) (%42 (\%248. ($1
       $0))))))`)
  val datatype_ptree = DT(["DISK_THM"], [], `(%235 ((%253 %114) %115))`)
  val ptree_11 =
    DT(["DISK_THM"], [],
       `((%15 (%42 (\%43. (%42 (\%254. ((%22 ((%85 (%114 $1)) (%114 $0)))
       ((%44 $1) $0))))))) (%16 (\%74. (%112 (\%108. (%16 (\%255. (%112
       (\%256. ((%22 ((%85 ((%115 $3) $2)) ((%115 $1) $0))) ((%15 ((%18 $3)
       $1)) ((%206 $2) $0))))))))))))`)
  val ptree_distinct =
    DT(["DISK_THM"], [],
       `(%112 (\%108. (%16 (\%74. (%42 (\%43. (%257 ((%85 (%114 $0)) ((%115
       $1) $2)))))))))`)
  val ptree_case_cong =
    DT(["DISK_THM"], [],
       `(%83 (\%258. (%83 (\%259. (%116 (\%117. (%118 (\%119. ((%6 ((%15
       ((%85 $3) $2)) ((%15 (%42 (\%43. ((%6 ((%85 $3) (%114 $0))) ((%29
       ($2 $0)) (%260 $0)))))) (%16 (\%74. (%112 (\%108. ((%6 ((%85 $4)
       ((%115 $1) $0))) ((%29 (($2 $1) $0)) ((%261 $1) $0)))))))))) ((%29
       (((%120 $1) $0) $3)) (((%120 %260) %261) $2)))))))))))`)
  val ptree_nchotomy =
    DT(["DISK_THM"], [],
       `(%83 (\%262. ((%64 (%65 (\%248. ((%85 $1) (%114 $0))))) (%73
       (\%216. (%263 (\%205. ((%85 $2) ((%115 $1) $0)))))))))`)
  val ptree_Axiom =
    DT(["DISK_THM"], [],
       `(%116 (\%264. (%265 (\%266. (%267 (\%268. (%269 (\%270. (%271
       (\%272. (%273 (\%274. ((%15 (%42 (\%43. ((%29 ($2 (%114 $0))) ($6
       $0))))) ((%15 (%16 (\%74. (%112 (\%108. ((%29 ($3 ((%115 $1) $0)))
       ((($6 $1) $0) ($2 $0)))))))) ((%15 ((%275 ($0 %111)) $3)) (%83
       (\%105. (%112 (\%108. ((%275 ($2 ((%113 $1) $0))) (((($4 $1) $0) ($3
       $1)) ($2 $0))))))))))))))))))))))`)
  val ptree_induction =
    DT(["DISK_THM"], [],
       `(%276 (\%277. (%278 (\%279. ((%6 ((%15 (%42 (\%248. ($2 (%114
       $0))))) ((%15 (%112 (\%205. ((%6 ($1 $0)) (%16 (\%216. ($3 ((%115
       $0) $1)))))))) ((%15 ($0 %111)) (%83 (\%262. (%112 (\%205. ((%6
       ((%15 ($3 $1)) ($2 $0))) ($2 ((%113 $1) $0))))))))))) ((%15 (%83
       (\%262. ($2 $0)))) (%112 (\%205. ($1 $0)))))))))`)
  val ptsizel_append =
    DT(["DISK_THM"], [],
       `((%31 (%139 ((%280 %281) %282))) ((%33 (%139 %281)) (%139 %282)))`)
  val getSymbols_ind =
    DT(["DISK_THM"], [],
       `(%278 (\%283. ((%6 ((%15 ($0 %111)) ((%15 (%42 (\%136. ($1 ((%113
       (%114 $0)) %111))))) ((%15 (%16 (\%123. (%112 (\%138. ($2 ((%113
       ((%115 $1) $0)) %111))))))) ((%15 (%42 (\%136. (%83 (\%151. (%112
       (\%150. ((%6 ($3 ((%113 $1) $0))) ($3 ((%113 (%114 $2)) ((%113 $1)
       $0))))))))))) (%16 (\%123. (%112 (\%138. (%83 (\%153. (%112 (\%152.
       ((%6 ($4 ((%113 $1) $0))) ($4 ((%113 ((%115 $3) $2)) ((%113 $1)
       $0))))))))))))))))) (%112 (\%284. ($1 $0))))))`)
  val getSymbols_def =
    DT(["DISK_THM"], [],
       `((%15 ((%231 (%145 %111)) %158)) ((%15 ((%231 (%145 ((%113 (%114
       %136)) %111))) ((%161 (%129 (%54 %136))) %158))) ((%15 ((%231 (%145
       ((%113 ((%115 %123) %138)) %111))) ((%161 (%127 (%55 %123))) %158)))
       ((%15 ((%231 (%145 ((%113 (%114 %136)) ((%113 %151) %150)))) ((%161
       (%129 (%54 %136))) (%145 ((%113 %151) %150))))) ((%231 (%145 ((%113
       ((%115 %123) %138)) ((%113 %153) %152)))) ((%161 (%127 (%55 %123)))
       (%145 ((%113 %153) %152))))))))`)
  val ptreeNodeSym_ind =
    DT(["DISK_THM"], [],
       `(%276 (\%285. ((%6 ((%15 (%28 (\%196. (%112 (\%194. ($2 ((%115 (%25
       $1)) $0))))))) (%28 (\%191. ($1 (%114 (%49 $0))))))) (%83 (\%159.
       ($1 $0))))))`)
  val ptreeNodeSym_def =
    DT(["DISK_THM"], [],
       `((%15 ((%125 (%183 ((%115 (%25 %196)) %194))) (%127 %196))) ((%125
       (%183 (%114 (%49 %191)))) (%129 %191)))`)
  val ptreeSubtSyms_ind =
    DT(["DISK_THM"], [],
       `(%276 (\%285. ((%6 ((%15 (%28 (\%196. (%112 (\%194. ($2 ((%115 (%25
       $1)) $0))))))) (%28 (\%191. ($1 (%114 (%49 $0))))))) (%83 (\%159.
       ($1 $0))))))`)
  val ptreeSubtSyms_def =
    DT(["DISK_THM"], [],
       `((%15 ((%231 (%198 ((%115 (%25 %196)) %194))) ((%203 %183) %194)))
       ((%231 (%198 (%114 (%49 %191)))) %158))`)
  val validptree =
    DT(["DISK_THM"], [],
       `((%15 ((%22 ((%230 %215) ((%115 %216) %124))) ((%15 ((%218 ((%170
       (%55 %216)) (%145 %124))) (%219 %215))) (%83 (\%217. ((%6 ((%220 $0)
       %124)) ((%6 (%132 $0)) ((%230 %215) $0)))))))) ((%22 ((%230 %215)
       (%114 %128))) %134))`)
  val validptree_ind =
    DT(["DISK_THM"], [],
       `(%286 (\%287. ((%6 ((%15 (%214 (\%215. (%16 (\%216. (%112 (\%124.
       ((%6 (%83 (\%217. ((%6 ((%15 ((%218 ((%170 (%55 $2)) (%145 $1)))
       (%219 $3))) ((%15 ((%220 $0) $1)) (%132 $0)))) (($4 $3) $0))))) (($3
       $2) ((%115 $1) $0)))))))))) (%214 (\%215. (%42 (\%128. (($2 $1)
       (%114 $0)))))))) (%214 (\%288. (%83 (\%225. (($2 $1) $0))))))))`)
  val flat_leaves =
    DT(["DISK_THM"], [],
       `(%112 (\%205. ((%231 (%232 ((%115 %216) $0))) (%289 ((%290 %232)
       $0)))))`)
  val getSyms_append =
    DT(["DISK_THM"], [],
       `((%231 (%145 ((%280 %281) %282))) ((%234 (%145 %281)) (%145
       %282)))`)
  val getSymsEqptree2Sym =
    DT(["DISK_THM"], [], `((%231 (%145 %205)) ((%203 %126) %205))`)
  val mapSymsptree =
    DT(["DISK_THM"], [],
       `((%231 ((%291 ((%292 %126) %293)) %294)) (%145 ((%295 %293)
       %294)))`)
  val getSyms_len =
    DT(["DISK_THM"], [],
       `(%112 (\%205. ((%31 (%296 $0)) (%297 (%145 $0)))))`)
  val take1_getSyms =
    DT(["DISK_THM"], [],
       `(%112 (\%205. (%298 (\%13. ((%6 ((%299 (%296 $1)) $0)) ((%231
       ((%300 $0) (%145 $1))) (%145 ((%301 $0) $1))))))))`)
  val take_getSyms =
    DT(["DISK_THM"], [],
       `(%298 (\%13. (%302 (\%303. ((%6 ((%304 ((%305 $1) ((%295 %293)
       $0))) (%306 %307))) ((%231 (%308 ((%309 $1) (%145 ((%295 %293)
       $0))))) (%145 (%310 ((%305 $1) ((%295 %293) $0))))))))))`)
  val checkRules_append =
    DT(["DISK_THM"], [],
       `((%22 ((%175 ((%311 %312) %313)) %314)) ((%15 ((%175 %312) %314))
       ((%175 %313) %314)))`)
  val ptreeToRules_append =
    DT(["DISK_THM"], [],
       `((%166 (%171 ((%280 %281) %282))) ((%172 (%171 %281)) (%171
       %282)))`)
  val getSyms_nil =
    DT(["DISK_THM"], [],
       `((%6 ((%231 (%145 %205)) %158)) ((%206 %205) %111))`)
  val getSyms_rev =
    DT(["DISK_THM"], [], `((%231 (%145 (%315 %307))) (%316 (%145 %307)))`)
  end
  val _ = DB.bindl "parseTree"
  [("nonTerminal_TY_DEF",nonTerminal_TY_DEF,DB.Def),
   ("nonTerminal_repfns",nonTerminal_repfns,DB.Def),
   ("parseTree0_def",parseTree0_def,DB.Def), ("NT",NT,DB.Def),
   ("nonTerminal_case_def",nonTerminal_case_def,DB.Def),
   ("nonTerminal_size_def",nonTerminal_size_def,DB.Def),
   ("terminal_TY_DEF",terminal_TY_DEF,DB.Def),
   ("terminal_repfns",terminal_repfns,DB.Def),
   ("parseTree1_def",parseTree1_def,DB.Def), ("TM",TM,DB.Def),
   ("terminal_case_def",terminal_case_def,DB.Def),
   ("terminal_size_def",terminal_size_def,DB.Def),
   ("tmnlToStr_def",tmnlToStr_def,DB.Def),
   ("nonTmnlToStr_def",nonTmnlToStr_def,DB.Def),
   ("ptree_TY_DEF",ptree_TY_DEF,DB.Def),
   ("ptree_repfns",ptree_repfns,DB.Def),
   ("listparseTree2_TY_DEF",listparseTree2_TY_DEF,DB.Def),
   ("listparseTree2_repfns",listparseTree2_repfns,DB.Def),
   ("parseTree3_def",parseTree3_def,DB.Def),
   ("parseTree4_def",parseTree4_def,DB.Def),
   ("parseTree5_def",parseTree5_def,DB.Def),
   ("parseTree6_def",parseTree6_def,DB.Def),
   ("parseTree7",parseTree7,DB.Def), ("Leaf",Leaf,DB.Def),
   ("Node",Node,DB.Def), ("ptree_case_def",ptree_case_def,DB.Def),
   ("ptree_size_def",ptree_size_def,DB.Def),
   ("ptree2Sym_def",ptree2Sym_def,DB.Def),
   ("isNode_def",isNode_def,DB.Def), ("isLeaf_def",isLeaf_def,DB.Def),
   ("ptsize_def",ptsize_def,DB.Def), ("ptheight_def",ptheight_def,DB.Def),
   ("getSymbols_primitive_def",getSymbols_primitive_def,DB.Def),
   ("ptreeToRules_def",ptreeToRules_def,DB.Def),
   ("checkRules_def",checkRules_def,DB.Def),
   ("ptreeNodeSym_primitive_def",ptreeNodeSym_primitive_def,DB.Def),
   ("ptreeSubtSyms_primitive_def",ptreeSubtSyms_primitive_def,DB.Def),
   ("ptreeSubtree_def",ptreeSubtree_def,DB.Def),
   ("validptree_defn_tupled_primitive_def",
    validptree_defn_tupled_primitive_def,
    DB.Def),
   ("validptree_defn_curried_def",validptree_defn_curried_def,DB.Def),
   ("leaves_def",leaves_def,DB.Def),
   ("datatype_nonTerminal",datatype_nonTerminal,DB.Thm),
   ("nonTerminal_11",nonTerminal_11,DB.Thm),
   ("nonTerminal_case_cong",nonTerminal_case_cong,DB.Thm),
   ("nonTerminal_nchotomy",nonTerminal_nchotomy,DB.Thm),
   ("nonTerminal_Axiom",nonTerminal_Axiom,DB.Thm),
   ("nonTerminal_induction",nonTerminal_induction,DB.Thm),
   ("datatype_terminal",datatype_terminal,DB.Thm),
   ("terminal_11",terminal_11,DB.Thm),
   ("terminal_case_cong",terminal_case_cong,DB.Thm),
   ("terminal_nchotomy",terminal_nchotomy,DB.Thm),
   ("terminal_Axiom",terminal_Axiom,DB.Thm),
   ("terminal_induction",terminal_induction,DB.Thm),
   ("datatype_ptree",datatype_ptree,DB.Thm), ("ptree_11",ptree_11,DB.Thm),
   ("ptree_distinct",ptree_distinct,DB.Thm),
   ("ptree_case_cong",ptree_case_cong,DB.Thm),
   ("ptree_nchotomy",ptree_nchotomy,DB.Thm),
   ("ptree_Axiom",ptree_Axiom,DB.Thm),
   ("ptree_induction",ptree_induction,DB.Thm),
   ("ptsizel_append",ptsizel_append,DB.Thm),
   ("getSymbols_ind",getSymbols_ind,DB.Thm),
   ("getSymbols_def",getSymbols_def,DB.Thm),
   ("ptreeNodeSym_ind",ptreeNodeSym_ind,DB.Thm),
   ("ptreeNodeSym_def",ptreeNodeSym_def,DB.Thm),
   ("ptreeSubtSyms_ind",ptreeSubtSyms_ind,DB.Thm),
   ("ptreeSubtSyms_def",ptreeSubtSyms_def,DB.Thm),
   ("validptree",validptree,DB.Thm),
   ("validptree_ind",validptree_ind,DB.Thm),
   ("flat_leaves",flat_leaves,DB.Thm),
   ("getSyms_append",getSyms_append,DB.Thm),
   ("getSymsEqptree2Sym",getSymsEqptree2Sym,DB.Thm),
   ("mapSymsptree",mapSymsptree,DB.Thm),
   ("getSyms_len",getSyms_len,DB.Thm),
   ("take1_getSyms",take1_getSyms,DB.Thm),
   ("take_getSyms",take_getSyms,DB.Thm),
   ("checkRules_append",checkRules_append,DB.Thm),
   ("ptreeToRules_append",ptreeToRules_append,DB.Thm),
   ("getSyms_nil",getSyms_nil,DB.Thm), ("getSyms_rev",getSyms_rev,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("grammarDefTheory.grammarDef_grammars",
                          grammarDefTheory.grammarDef_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "nonTerminal"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_nonTerminal")
        {Name = "dest_nonTerminal", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_nonTerminal")
        {Name = "mk_nonTerminal", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree0")
        {Name = "parseTree0", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NT")
        {Name = "NT", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nonTerminal_case")
        {Name = "nonTerminal_case", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nonTerminal_size")
        {Name = "nonTerminal_size", Thy = "parseTree"}
  val _ = update_grms temp_add_type "terminal"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_terminal")
        {Name = "dest_terminal", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_terminal")
        {Name = "mk_terminal", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree1")
        {Name = "parseTree1", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "TM")
        {Name = "TM", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "terminal_case")
        {Name = "terminal_case", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "terminal_size")
        {Name = "terminal_size", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "tmnlToStr")
        {Name = "tmnlToStr", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "nonTmnlToStr")
        {Name = "nonTmnlToStr", Thy = "parseTree"}
  val _ = update_grms temp_add_type "ptree"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_ptree")
        {Name = "dest_ptree", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_ptree")
        {Name = "mk_ptree", Thy = "parseTree"}
  val _ = update_grms temp_add_type "listparseTree2"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_listparseTree2")
        {Name = "dest_listparseTree2", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_listparseTree2")
        {Name = "mk_listparseTree2", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree3")
        {Name = "parseTree3", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree4")
        {Name = "parseTree4", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree5")
        {Name = "parseTree5", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree6")
        {Name = "parseTree6", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parseTree7")
        {Name = "parseTree7", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Leaf")
        {Name = "Leaf", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "Node")
        {Name = "Node", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptree_case")
        {Name = "ptree_case", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptree_size")
        {Name = "ptree_size", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptree1_size")
        {Name = "ptree1_size", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptree2Sym")
        {Name = "ptree2Sym", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isNode")
        {Name = "isNode", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "isLeaf")
        {Name = "isLeaf", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptsize")
        {Name = "ptsize", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptsizel")
        {Name = "ptsizel", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptheight")
        {Name = "ptheight", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptheightl")
        {Name = "ptheightl", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "getSymbols")
        {Name = "getSymbols", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptreeToRules")
        {Name = "ptreeToRules", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptreeToRules2")
        {Name = "ptreeToRules2", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "checkRules")
        {Name = "checkRules", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptreeNodeSym")
        {Name = "ptreeNodeSym", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptreeSubtSyms")
        {Name = "ptreeSubtSyms", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "ptreeSubtree")
        {Name = "ptreeSubtree", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validptree_defn_tupled")
        {Name = "validptree_defn_tupled", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "validptree")
        {Name = "validptree", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "leaves")
        {Name = "leaves", Thy = "parseTree"}
  val _ = update_grms
       (temp_overload_on_by_nametype "cleaves")
        {Name = "cleaves", Thy = "parseTree"}
  val parseTree_grammars = Parse.current_lgrms()
  end
  
  
  val parseTree_rwts = simpLib.rewrites [
            ptsize_def];
  val _ = BasicProvers.augment_srw_ss [parseTree_rwts]

  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG nonTerminal_Axiom,
           case_def=nonTerminal_case_def,
           case_cong=nonTerminal_case_cong,
           induction=ORIG nonTerminal_induction,
           nchotomy=nonTerminal_nchotomy,
           size=SOME(Parse.Term`(parseTree$nonTerminal_size) :(parseTree$nonTerminal) -> (num$num)`,
                     ORIG nonTerminal_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME nonTerminal_11,
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
          {ax=ORIG terminal_Axiom,
           case_def=terminal_case_def,
           case_cong=terminal_case_cong,
           induction=ORIG terminal_induction,
           nchotomy=terminal_nchotomy,
           size=SOME(Parse.Term`(parseTree$terminal_size) :(parseTree$terminal) -> (num$num)`,
                     ORIG terminal_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME terminal_11,
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
  
  
  val _ = computeLib.add_funs [tmnlToStr_def];  
  
  val _ = computeLib.add_funs [nonTmnlToStr_def];  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG ptree_Axiom,
           case_def=ptree_case_def,
           case_cong=ptree_case_cong,
           induction=ORIG ptree_induction,
           nchotomy=ptree_nchotomy,
           size=SOME(Parse.Term`(parseTree$ptree_size) :(parseTree$ptree) -> (num$num)`,
                     ORIG ptree_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME ptree_11,
           distinct=SOME ptree_distinct,
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
  
  
  val _ = computeLib.add_funs [ptree2Sym_def];  
  
  val _ = computeLib.add_funs [isNode_def];  
  
  val _ = computeLib.add_funs [isLeaf_def];  
  
  val _ = computeLib.add_funs [ptsize_def];  
  
  val _ = computeLib.add_funs [ptheight_def];  
  
  val _ = computeLib.add_funs [getSymbols_def];  
  
  val _ = computeLib.add_funs [ptreeToRules_def];  
  
  val _ = computeLib.add_funs [checkRules_def];  
  
  val _ = computeLib.add_funs [ptreeNodeSym_def];  
  
  val _ = computeLib.add_funs [ptreeSubtSyms_def];  
  
  val _ = computeLib.add_funs [ptreeSubtree_def];  
  
  val _ = computeLib.add_funs [leaves_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
