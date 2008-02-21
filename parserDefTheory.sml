structure parserDefTheory :> parserDefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading parserDefTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open parseTreeTheory whileLemmasTheory
  in end;
  val _ = Theory.link_parents
          ("parserDef",
          Arbnum.fromString "1203551171",
          Arbnum.fromString "311592")
          [("parseTree",
           Arbnum.fromString "1203551154",
           Arbnum.fromString "487819"),
           ("whileLemmas",
           Arbnum.fromString "1203551036",
           Arbnum.fromString "20137")];
  val _ = Theory.incorporate_types "parserDef"
       [("action",0), ("state",0), ("item",0)];
  val _ = Theory.incorporate_consts "parserDef"
     [("stateSym",((T"state" "parserDef" [] --> T"symbol" "regexp" []))),
      ("stateItl",
       ((T"state" "parserDef" [] -->
         T"list" "list" [T"item" "parserDef" []]))),
      ("item_size",((T"item" "parserDef" [] --> T"num" "num" []))),
      ("mk_item",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"string" "string" [],
             T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"list" "list" [T"symbol" "regexp" []]]]] -->
         T"item" "parserDef" []))),
      ("REDUCE",((T"rule" "grammarDef" [] --> T"action" "parserDef" []))),
      ("mk_state",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"symbol" "regexp" [],
             T"list" "list" [T"item" "parserDef" []]]] -->
         T"state" "parserDef" []))),
      ("action_case",
       (((T"rule" "grammarDef" [] --> alpha) -->
         ((T"state" "parserDef" [] --> alpha) -->
          (alpha --> (T"action" "parserDef" [] --> alpha)))))),
      ("dest_action",
       ((T"action" "parserDef" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"rule" "grammarDef" [], T"state" "parserDef" []]]))),
      ("state_case",
       (((T"symbol" "regexp" [] -->
          (T"list" "list" [T"item" "parserDef" []] --> alpha)) -->
         (T"state" "parserDef" [] --> alpha)))),
      ("item",
       ((T"string" "string" [] -->
         (T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]] -->
          T"item" "parserDef" [])))),
      ("state",
       ((T"symbol" "regexp" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          T"state" "parserDef" [])))),
      ("dest_state",
       ((T"state" "parserDef" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"symbol" "regexp" [],
             T"list" "list" [T"item" "parserDef" []]]]))),
      ("action_size",((T"action" "parserDef" [] --> T"num" "num" []))),
      ("mk_action",
       ((T"recspace" "ind_type"
          [T"prod" "pair"
            [T"rule" "grammarDef" [], T"state" "parserDef" []]] -->
         T"action" "parserDef" []))),
      ("item_case",
       (((T"string" "string" [] -->
          (T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]] --> alpha)) -->
         (T"item" "parserDef" [] --> alpha)))),
      ("state_size",((T"state" "parserDef" [] --> T"num" "num" []))),
      ("NA",(T"action" "parserDef" [])),
      ("GOTO",((T"state" "parserDef" [] --> T"action" "parserDef" []))),
      ("parserDef4",(T"action" "parserDef" [])),
      ("parserDef3",
       ((T"state" "parserDef" [] --> T"action" "parserDef" []))),
      ("parserDef2",
       ((T"rule" "grammarDef" [] --> T"action" "parserDef" []))),
      ("parserDef1",
       ((T"symbol" "regexp" [] -->
         (T"list" "list" [T"item" "parserDef" []] -->
          T"state" "parserDef" [])))),
      ("parserDef0",
       ((T"string" "string" [] -->
         (T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]] -->
          T"item" "parserDef" [])))),
      ("dest_item",
       ((T"item" "parserDef" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"string" "string" [],
             T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"list" "list" [T"symbol" "regexp" []]]]])))];
  
  local
  val share_table = Vector.fromList
  [C"?" "bool"
    ((((T"item" "parserDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]]]) --> bool) -->
      bool)),
   V"rep"
    ((T"item" "parserDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"string" "string" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]]] --> bool) -->
      ((T"item" "parserDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]]] --> bool) --> bool)
      --> bool)),
   V"'item'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]]] --> bool)),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"string" "string" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]]] --> bool) -->
      bool)), C"?" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"a0" (T"string" "string" []),
   C"?" "bool"
    (((T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool) --> bool)),
   V"a1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]]] -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"string" "string" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]]] --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"string" "string" [],
             T"prod" "pair"
              [T"list" "list" [T"symbol" "regexp" []],
               T"list" "list" [T"symbol" "regexp" []]]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"string" "string" [],
            T"prod" "pair"
             [T"list" "list" [T"symbol" "regexp" []],
              T"list" "list" [T"symbol" "regexp" []]]]])))),
   C"0" "num" (T"num" "num" []),
   C"," "pair"
    ((T"string" "string" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]]))),
   V"n" (T"num" "num" []),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]]]),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((T"item" "parserDef" [] --> bool) --> bool)),
   V"a" (T"item" "parserDef" []),
   C"=" "min"
    ((T"item" "parserDef" [] --> (T"item" "parserDef" [] --> bool))),
   C"mk_item" "parserDef"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]]] -->
      T"item" "parserDef" [])),
   C"dest_item" "parserDef"
    ((T"item" "parserDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"string" "string" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"string" "string" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]]]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] -->
        T"item" "parserDef" [])) -->
      ((T"string" "string" [] -->
        (T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]] -->
         T"item" "parserDef" [])) --> bool))),
   C"parserDef0" "parserDef"
    ((T"string" "string" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"item" "parserDef" []))),
   C"item" "parserDef"
    ((T"string" "string" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"item" "parserDef" []))),
   C"!" "bool"
    ((((T"string" "string" [] -->
        (T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]] --> alpha)) --> bool)
      --> bool)),
   V"f"
    ((T"string" "string" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> alpha))),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   C"!" "bool"
    (((T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool) --> bool)),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"item_case" "parserDef"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] --> alpha)) -->
      (T"item" "parserDef" [] --> alpha))),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"item_size" "parserDef" ((T"item" "parserDef" [] --> T"num" "num" [])),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"string_size" "string" ((T"string" "string" [] --> T"num" "num" [])),
   C"pair_size" "basicSize"
    (((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" []) -->
      ((T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" []) -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] --> T"num" "num" [])))),
   C"list_size" "list"
    (((T"symbol" "regexp" [] --> T"num" "num" []) -->
      (T"list" "list" [T"symbol" "regexp" []] --> T"num" "num" []))),
   C"symbol_size" "regexp" ((T"symbol" "regexp" [] --> T"num" "num" [])),
   C"?" "bool"
    ((((T"state" "parserDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"symbol" "regexp" [],
            T"list" "list" [T"item" "parserDef" []]]]) --> bool) -->
      bool)),
   V"rep"
    ((T"state" "parserDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"symbol" "regexp" [],
          T"list" "list" [T"item" "parserDef" []]]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]
       --> bool) -->
      ((T"state" "parserDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"symbol" "regexp" [],
            T"list" "list" [T"item" "parserDef" []]]]) --> bool))),
   V"a0'"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"symbol" "regexp" [],
            T"list" "list" [T"item" "parserDef" []]]] --> bool) --> bool)
      --> bool)),
   V"'state'"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]
      --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]
       --> bool) --> bool)),
   C"?" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"a0" (T"symbol" "regexp" []),
   C"?" "bool"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   V"a1" (T"list" "list" [T"item" "parserDef" []]),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]
      -->
      (T"recspace" "ind_type"
        [T"prod" "pair"
          [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]
       --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]
       -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"symbol" "regexp" [],
             T"list" "list" [T"item" "parserDef" []]]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"symbol" "regexp" [],
            T"list" "list" [T"item" "parserDef" []]]])))),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"prod" "pair"
        [T"symbol" "regexp" [],
         T"list" "list" [T"item" "parserDef" []]]))),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]),
   C"!" "bool" (((T"state" "parserDef" [] --> bool) --> bool)),
   V"a" (T"state" "parserDef" []),
   C"=" "min"
    ((T"state" "parserDef" [] --> (T"state" "parserDef" [] --> bool))),
   C"mk_state" "parserDef"
    ((T"recspace" "ind_type"
       [T"prod" "pair"
         [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]
      --> T"state" "parserDef" [])),
   C"dest_state" "parserDef"
    ((T"state" "parserDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"symbol" "regexp" [],
          T"list" "list" [T"item" "parserDef" []]]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair"
        [T"symbol" "regexp" [], T"list" "list" [T"item" "parserDef" []]]]),
   C"=" "min"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"state" "parserDef" [])) -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"item" "parserDef" []] -->
         T"state" "parserDef" [])) --> bool))),
   C"parserDef1" "parserDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"state" "parserDef" []))),
   C"state" "parserDef"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] -->
       T"state" "parserDef" []))),
   C"!" "bool"
    ((((T"symbol" "regexp" [] -->
        (T"list" "list" [T"item" "parserDef" []] --> alpha)) --> bool) -->
      bool)),
   V"f"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> alpha))),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   C"!" "bool"
    (((T"list" "list" [T"item" "parserDef" []] --> bool) --> bool)),
   C"state_case" "parserDef"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] --> alpha)) -->
      (T"state" "parserDef" [] --> alpha))),
   C"state_size" "parserDef"
    ((T"state" "parserDef" [] --> T"num" "num" [])),
   C"list_size" "list"
    (((T"item" "parserDef" [] --> T"num" "num" []) -->
      (T"list" "list" [T"item" "parserDef" []] --> T"num" "num" []))),
   C"?" "bool"
    ((((T"action" "parserDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"rule" "grammarDef" [], T"state" "parserDef" []]]) --> bool)
      --> bool)),
   V"rep"
    ((T"action" "parserDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"rule" "grammarDef" [], T"state" "parserDef" []]])),
   C"TYPE_DEFINITION" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]
       --> bool) -->
      ((T"action" "parserDef" [] -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"rule" "grammarDef" [], T"state" "parserDef" []]]) -->
       bool))),
   V"a0"
    (T"recspace" "ind_type"
      [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]),
   C"!" "bool"
    ((((T"recspace" "ind_type"
         [T"prod" "pair"
           [T"rule" "grammarDef" [], T"state" "parserDef" []]] --> bool)
       --> bool) --> bool)),
   V"'action'"
    ((T"recspace" "ind_type"
       [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]
      --> bool)),
   C"!" "bool"
    (((T"recspace" "ind_type"
        [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]
       --> bool) --> bool)), C"\\/" "bool" ((bool --> (bool --> bool))),
   C"?" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   V"a" (T"rule" "grammarDef" []),
   C"=" "min"
    ((T"recspace" "ind_type"
       [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]
      -->
      (T"recspace" "ind_type"
        [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]
       --> bool))),
   C"CONSTR" "ind_type"
    ((T"num" "num" [] -->
      (T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]
       -->
       ((T"num" "num" [] -->
         T"recspace" "ind_type"
          [T"prod" "pair"
            [T"rule" "grammarDef" [], T"state" "parserDef" []]]) -->
        T"recspace" "ind_type"
         [T"prod" "pair"
           [T"rule" "grammarDef" [], T"state" "parserDef" []]])))),
   C"," "pair"
    ((T"rule" "grammarDef" [] -->
      (T"state" "parserDef" [] -->
       T"prod" "pair"
        [T"rule" "grammarDef" [], T"state" "parserDef" []]))),
   C"@" "min"
    (((T"state" "parserDef" [] --> bool) --> T"state" "parserDef" [])),
   V"v" (T"state" "parserDef" []), C"T" "bool" (bool),
   C"BOTTOM" "ind_type"
    (T"recspace" "ind_type"
      [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]),
   C"?" "bool" (((T"state" "parserDef" [] --> bool) --> bool)),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"@" "min"
    (((T"rule" "grammarDef" [] --> bool) --> T"rule" "grammarDef" [])),
   V"v" (T"rule" "grammarDef" []),
   C"!" "bool" (((T"action" "parserDef" [] --> bool) --> bool)),
   V"a" (T"action" "parserDef" []),
   C"=" "min"
    ((T"action" "parserDef" [] --> (T"action" "parserDef" [] --> bool))),
   C"mk_action" "parserDef"
    ((T"recspace" "ind_type"
       [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]
      --> T"action" "parserDef" [])),
   C"dest_action" "parserDef"
    ((T"action" "parserDef" [] -->
      T"recspace" "ind_type"
       [T"prod" "pair"
         [T"rule" "grammarDef" [], T"state" "parserDef" []]])),
   V"r"
    (T"recspace" "ind_type"
      [T"prod" "pair" [T"rule" "grammarDef" [], T"state" "parserDef" []]]),
   C"=" "min"
    (((T"rule" "grammarDef" [] --> T"action" "parserDef" []) -->
      ((T"rule" "grammarDef" [] --> T"action" "parserDef" []) --> bool))),
   C"parserDef2" "parserDef"
    ((T"rule" "grammarDef" [] --> T"action" "parserDef" [])),
   C"=" "min"
    (((T"state" "parserDef" [] --> T"action" "parserDef" []) -->
      ((T"state" "parserDef" [] --> T"action" "parserDef" []) --> bool))),
   C"parserDef3" "parserDef"
    ((T"state" "parserDef" [] --> T"action" "parserDef" [])),
   C"parserDef4" "parserDef" (T"action" "parserDef" []),
   C"REDUCE" "parserDef"
    ((T"rule" "grammarDef" [] --> T"action" "parserDef" [])),
   C"GOTO" "parserDef"
    ((T"state" "parserDef" [] --> T"action" "parserDef" [])),
   C"NA" "parserDef" (T"action" "parserDef" []),
   C"!" "bool" ((((T"rule" "grammarDef" [] --> alpha) --> bool) --> bool)),
   V"f" ((T"rule" "grammarDef" [] --> alpha)),
   C"!" "bool" ((((T"state" "parserDef" [] --> alpha) --> bool) --> bool)),
   V"f1" ((T"state" "parserDef" [] --> alpha)),
   C"!" "bool" (((alpha --> bool) --> bool)), V"v" (alpha),
   C"!" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   C"action_case" "parserDef"
    (((T"rule" "grammarDef" [] --> alpha) -->
      ((T"state" "parserDef" [] --> alpha) -->
       (alpha --> (T"action" "parserDef" [] --> alpha))))),
   C"action_size" "parserDef"
    ((T"action" "parserDef" [] --> T"num" "num" [])),
   C"rule_size" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"num" "num" [])),
   V"sym" (T"symbol" "regexp" []),
   V"itl" (T"list" "list" [T"item" "parserDef" []]),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"stateSym" "parserDef"
    ((T"state" "parserDef" [] --> T"symbol" "regexp" [])),
   C"=" "min"
    ((T"list" "list" [T"item" "parserDef" []] -->
      (T"list" "list" [T"item" "parserDef" []] --> bool))),
   C"stateItl" "parserDef"
    ((T"state" "parserDef" [] -->
      T"list" "list" [T"item" "parserDef" []])),
   C"DATATYPE" "bool" ((bool --> bool)),
   V"item"
    (((T"string" "string" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] -->
        T"item" "parserDef" [])) --> bool)),
   V"a0'" (T"string" "string" []),
   V"a1'"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"=" "min"
    ((T"string" "string" [] --> (T"string" "string" [] --> bool))),
   C"=" "min"
    ((T"prod" "pair"
       [T"list" "list" [T"symbol" "regexp" []],
        T"list" "list" [T"symbol" "regexp" []]] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   V"M" (T"item" "parserDef" []), V"M'" (T"item" "parserDef" []),
   V"f'"
    ((T"string" "string" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] --> alpha))),
   V"i" (T"item" "parserDef" []), V"s" (T"string" "string" []),
   V"p"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"?" "bool" ((((T"item" "parserDef" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"item" "parserDef" [] --> alpha)),
   C"!" "bool" ((((T"item" "parserDef" [] --> bool) --> bool) --> bool)),
   V"P" ((T"item" "parserDef" [] --> bool)),
   V"state"
    (((T"symbol" "regexp" [] -->
       (T"list" "list" [T"item" "parserDef" []] -->
        T"state" "parserDef" [])) --> bool)),
   V"a0'" (T"symbol" "regexp" []),
   V"a1'" (T"list" "list" [T"item" "parserDef" []]),
   V"M" (T"state" "parserDef" []), V"M'" (T"state" "parserDef" []),
   V"f'"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"item" "parserDef" []] --> alpha))),
   V"s" (T"state" "parserDef" []), V"s" (T"symbol" "regexp" []),
   V"l" (T"list" "list" [T"item" "parserDef" []]),
   C"?" "bool" ((((T"state" "parserDef" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"state" "parserDef" [] --> alpha)),
   C"!" "bool" ((((T"state" "parserDef" [] --> bool) --> bool) --> bool)),
   V"P" ((T"state" "parserDef" [] --> bool)),
   V"action"
    (((T"rule" "grammarDef" [] --> T"action" "parserDef" []) -->
      ((T"state" "parserDef" [] --> T"action" "parserDef" []) -->
       (T"action" "parserDef" [] --> bool)))),
   V"a'" (T"rule" "grammarDef" []),
   C"=" "min"
    ((T"rule" "grammarDef" [] --> (T"rule" "grammarDef" [] --> bool))),
   V"a'" (T"state" "parserDef" []), C"~" "bool" ((bool --> bool)),
   V"M" (T"action" "parserDef" []), V"M'" (T"action" "parserDef" []),
   V"f'" ((T"rule" "grammarDef" [] --> alpha)),
   V"f1'" ((T"state" "parserDef" [] --> alpha)), V"v'" (alpha),
   V"r" (T"rule" "grammarDef" []),
   V"f0" ((T"rule" "grammarDef" [] --> alpha)), V"f2" (alpha),
   C"?" "bool"
    ((((T"action" "parserDef" [] --> alpha) --> bool) --> bool)),
   V"fn" ((T"action" "parserDef" [] --> alpha)),
   C"!" "bool" ((((T"action" "parserDef" [] --> bool) --> bool) --> bool)),
   V"P" ((T"action" "parserDef" [] --> bool))]
  val DT = Thm.disk_thm share_table
  in
  val item_TY_DEF =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 (%8 (\%9. (%10
       (\%11. ((%12 $2) (((\%9. (\%11. (((%13 %14) ((%15 $1) $0)) (\%16.
       %17)))) $1) $0))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val item_repfns =
    DT(["DISK_THM"], [],
       `((%18 (%19 (\%20. ((%21 (%22 (%23 $0))) $0)))) (%7 (\%24. ((%25
       ((\%3. (%4 (\%5. ((%6 (%7 (\%3. ((%6 (%8 (\%9. (%10 (\%11. ((%12 $2)
       (((\%9. (\%11. (((%13 %14) ((%15 $1) $0)) (\%16. %17)))) $1)
       $0))))))) ($1 $0))))) ($0 $1))))) $0)) ((%12 (%23 (%22 $0)))
       $0)))))`)
  val parserDef0_def =
    DT([], [],
       `((%26 %27) (\%9. (\%11. (%22 (((\%9. (\%11. (((%13 %14) ((%15 $1)
       $0)) (\%16. %17)))) $1) $0)))))`)
  val item = DT([], [], `((%26 %28) %27)`)
  val item_case_def =
    DT(["DISK_THM"], [],
       `(%29 (\%30. (%31 (\%9. (%32 (\%11. ((%33 ((%34 $2) ((%28 $1) $0)))
       (($2 $1) $0))))))))`)
  val item_size_def =
    DT(["DISK_THM"], [],
       `(%31 (\%9. (%32 (\%11. ((%35 (%36 ((%28 $1) $0))) ((%37 (%38 (%39
       %40))) ((%37 (%41 $1)) (((%42 (%43 %44)) (%43 %44)) $0))))))))`)
  val state_TY_DEF =
    DT(["DISK_THM"], [],
       `(%45 (\%46. ((%47 (\%48. (%49 (\%50. ((%6 (%51 (\%48. ((%6 (%52
       (\%53. (%54 (\%55. ((%56 $2) (((\%53. (\%55. (((%57 %14) ((%58 $1)
       $0)) (\%16. %59)))) $1) $0))))))) ($1 $0))))) ($0 $1)))))) $0)))`)
  val state_repfns =
    DT(["DISK_THM"], [],
       `((%18 (%60 (\%61. ((%62 (%63 (%64 $0))) $0)))) (%51 (\%65. ((%25
       ((\%48. (%49 (\%50. ((%6 (%51 (\%48. ((%6 (%52 (\%53. (%54 (\%55.
       ((%56 $2) (((\%53. (\%55. (((%57 %14) ((%58 $1) $0)) (\%16. %59))))
       $1) $0))))))) ($1 $0))))) ($0 $1))))) $0)) ((%56 (%64 (%63 $0)))
       $0)))))`)
  val parserDef1_def =
    DT([], [],
       `((%66 %67) (\%53. (\%55. (%63 (((\%53. (\%55. (((%57 %14) ((%58 $1)
       $0)) (\%16. %59)))) $1) $0)))))`)
  val state = DT([], [], `((%66 %68) %67)`)
  val state_case_def =
    DT(["DISK_THM"], [],
       `(%69 (\%70. (%71 (\%53. (%72 (\%55. ((%33 ((%73 $2) ((%68 $1) $0)))
       (($2 $1) $0))))))))`)
  val state_size_def =
    DT(["DISK_THM"], [],
       `(%71 (\%53. (%72 (\%55. ((%35 (%74 ((%68 $1) $0))) ((%37 (%38 (%39
       %40))) ((%37 (%44 $1)) ((%75 %36) $0))))))))`)
  val action_TY_DEF =
    DT(["DISK_THM"], [],
       `(%76 (\%77. ((%78 (\%79. (%80 (\%81. ((%6 (%82 (\%79. ((%6 ((%83
       (%84 (\%85. ((%86 $1) ((\%85. (((%87 %14) ((%88 $0) (%89 (\%90.
       %91)))) (\%16. %92))) $0))))) ((%83 (%93 (\%61. ((%86 $1) ((\%61.
       (((%87 (%94 %14)) ((%88 (%95 (\%96. %91))) $0)) (\%16. %92)))
       $0))))) ((%86 $0) (((%87 (%94 (%94 %14))) ((%88 (%95 (\%96. %91)))
       (%89 (\%90. %91)))) (\%16. %92)))))) ($1 $0))))) ($0 $1))))))
       $0)))`)
  val action_repfns =
    DT(["DISK_THM"], [],
       `((%18 (%97 (\%98. ((%99 (%100 (%101 $0))) $0)))) (%82 (\%102. ((%25
       ((\%79. (%80 (\%81. ((%6 (%82 (\%79. ((%6 ((%83 (%84 (\%85. ((%86
       $1) ((\%85. (((%87 %14) ((%88 $0) (%89 (\%90. %91)))) (\%16. %92)))
       $0))))) ((%83 (%93 (\%61. ((%86 $1) ((\%61. (((%87 (%94 %14)) ((%88
       (%95 (\%96. %91))) $0)) (\%16. %92))) $0))))) ((%86 $0) (((%87 (%94
       (%94 %14))) ((%88 (%95 (\%96. %91))) (%89 (\%90. %91)))) (\%16.
       %92)))))) ($1 $0))))) ($0 $1))))) $0)) ((%86 (%101 (%100 $0)))
       $0)))))`)
  val parserDef2_def =
    DT([], [],
       `((%103 %104) (\%85. (%100 ((\%85. (((%87 %14) ((%88 $0) (%89 (\%90.
       %91)))) (\%16. %92))) $0))))`)
  val parserDef3_def =
    DT([], [],
       `((%105 %106) (\%61. (%100 ((\%61. (((%87 (%94 %14)) ((%88 (%95
       (\%96. %91))) $0)) (\%16. %92))) $0))))`)
  val parserDef4_def =
    DT([], [],
       `((%99 %107) (%100 (((%87 (%94 (%94 %14))) ((%88 (%95 (\%96. %91)))
       (%89 (\%90. %91)))) (\%16. %92))))`)
  val REDUCE = DT([], [], `((%103 %108) %104)`)
  val GOTO = DT([], [], `((%105 %109) %106)`)
  val NA = DT([], [], `((%99 %110) %107)`)
  val action_case_def =
    DT(["DISK_THM"], [],
       `((%18 (%111 (\%112. (%113 (\%114. (%115 (\%116. (%117 (\%85. ((%33
       ((((%118 $3) $2) $1) (%108 $0))) ($3 $0))))))))))) ((%18 (%111
       (\%112. (%113 (\%114. (%115 (\%116. (%60 (\%61. ((%33 ((((%118 $3)
       $2) $1) (%109 $0))) ($2 $0))))))))))) (%111 (\%112. (%113 (\%114.
       (%115 (\%116. ((%33 ((((%118 $2) $1) $0) %110)) $0)))))))))`)
  val action_size_def =
    DT(["DISK_THM"], [],
       `((%18 (%117 (\%85. ((%35 (%119 (%108 $0))) ((%37 (%38 (%39 %40)))
       (%120 $0)))))) ((%18 (%60 (\%61. ((%35 (%119 (%109 $0))) ((%37 (%38
       (%39 %40))) (%74 $0)))))) ((%35 (%119 %110)) %14)))`)
  val stateSym_def =
    DT(["DISK_THM"], [],
       `(%71 (\%121. (%72 (\%122. ((%123 (%124 ((%68 $1) $0))) $1)))))`)
  val stateItl_def =
    DT(["DISK_THM"], [],
       `(%71 (\%121. (%72 (\%122. ((%125 (%126 ((%68 $1) $0))) $0)))))`)
  val datatype_item = DT(["DISK_THM"], [], `(%127 (%128 %28))`)
  val item_11 =
    DT(["DISK_THM"], [],
       `(%31 (\%9. (%32 (\%11. (%31 (\%129. (%32 (\%130. ((%25 ((%21 ((%28
       $3) $2)) ((%28 $1) $0))) ((%18 ((%131 $3) $1)) ((%132 $2)
       $0)))))))))))`)
  val item_case_cong =
    DT(["DISK_THM"], [],
       `(%19 (\%133. (%19 (\%134. (%29 (\%30. ((%6 ((%18 ((%21 $2) $1))
       (%31 (\%9. (%32 (\%11. ((%6 ((%21 $3) ((%28 $1) $0))) ((%33 (($2 $1)
       $0)) ((%135 $1) $0))))))))) ((%33 ((%34 $0) $2)) ((%34 %135)
       $1)))))))))`)
  val item_nchotomy =
    DT(["DISK_THM"], [],
       `(%19 (\%136. (%8 (\%137. (%10 (\%138. ((%21 $2) ((%28 $1)
       $0))))))))`)
  val item_Axiom =
    DT(["DISK_THM"], [],
       `(%29 (\%30. (%139 (\%140. (%31 (\%9. (%32 (\%11. ((%33 ($2 ((%28
       $1) $0))) (($3 $1) $0))))))))))`)
  val item_induction =
    DT(["DISK_THM"], [],
       `(%141 (\%142. ((%6 (%31 (\%137. (%32 (\%138. ($2 ((%28 $1)
       $0))))))) (%19 (\%136. ($1 $0))))))`)
  val datatype_state = DT(["DISK_THM"], [], `(%127 (%143 %68))`)
  val state_11 =
    DT(["DISK_THM"], [],
       `(%71 (\%53. (%72 (\%55. (%71 (\%144. (%72 (\%145. ((%25 ((%62 ((%68
       $3) $2)) ((%68 $1) $0))) ((%18 ((%123 $3) $1)) ((%125 $2)
       $0)))))))))))`)
  val state_case_cong =
    DT(["DISK_THM"], [],
       `(%60 (\%146. (%60 (\%147. (%69 (\%70. ((%6 ((%18 ((%62 $2) $1))
       (%71 (\%53. (%72 (\%55. ((%6 ((%62 $3) ((%68 $1) $0))) ((%33 (($2
       $1) $0)) ((%148 $1) $0))))))))) ((%33 ((%73 $0) $2)) ((%73 %148)
       $1)))))))))`)
  val state_nchotomy =
    DT(["DISK_THM"], [],
       `(%60 (\%149. (%52 (\%150. (%54 (\%151. ((%62 $2) ((%68 $1)
       $0))))))))`)
  val state_Axiom =
    DT(["DISK_THM"], [],
       `(%69 (\%70. (%152 (\%153. (%71 (\%53. (%72 (\%55. ((%33 ($2 ((%68
       $1) $0))) (($3 $1) $0))))))))))`)
  val state_induction =
    DT(["DISK_THM"], [],
       `(%154 (\%155. ((%6 (%71 (\%150. (%72 (\%151. ($2 ((%68 $1)
       $0))))))) (%60 (\%149. ($1 $0))))))`)
  val datatype_action =
    DT(["DISK_THM"], [], `(%127 (((%156 %108) %109) %110))`)
  val action_11 =
    DT(["DISK_THM"], [],
       `((%18 (%117 (\%85. (%117 (\%157. ((%25 ((%99 (%108 $1)) (%108 $0)))
       ((%158 $1) $0))))))) (%60 (\%61. (%60 (\%159. ((%25 ((%99 (%109 $1))
       (%109 $0))) ((%62 $1) $0)))))))`)
  val action_distinct =
    DT(["DISK_THM"], [],
       `((%18 (%60 (\%159. (%117 (\%85. (%160 ((%99 (%108 $0)) (%109
       $1)))))))) ((%18 (%117 (\%85. (%160 ((%99 (%108 $0)) %110))))) (%60
       (\%61. (%160 ((%99 (%109 $0)) %110))))))`)
  val action_case_cong =
    DT(["DISK_THM"], [],
       `(%97 (\%161. (%97 (\%162. (%111 (\%112. (%113 (\%114. (%115 (\%116.
       ((%6 ((%18 ((%99 $4) $3)) ((%18 (%117 (\%85. ((%6 ((%99 $4) (%108
       $0))) ((%33 ($3 $0)) (%163 $0)))))) ((%18 (%60 (\%61. ((%6 ((%99 $4)
       (%109 $0))) ((%33 ($2 $0)) (%164 $0)))))) ((%6 ((%99 $3) %110))
       ((%33 $0) %165)))))) ((%33 ((((%118 $2) $1) $0) $4)) ((((%118 %163)
       %164) %165) $3)))))))))))))`)
  val action_nchotomy =
    DT(["DISK_THM"], [],
       `(%97 (\%98. ((%83 (%84 (\%166. ((%99 $1) (%108 $0))))) ((%83 (%93
       (\%149. ((%99 $1) (%109 $0))))) ((%99 $0) %110)))))`)
  val action_Axiom =
    DT(["DISK_THM"], [],
       `(%111 (\%167. (%113 (\%114. (%115 (\%168. (%169 (\%170. ((%18 (%117
       (\%85. ((%33 ($1 (%108 $0))) ($4 $0))))) ((%18 (%60 (\%61. ((%33 ($1
       (%109 $0))) ($3 $0))))) ((%33 ($0 %110)) $1)))))))))))`)
  val action_induction =
    DT(["DISK_THM"], [],
       `(%171 (\%172. ((%6 ((%18 (%117 (\%166. ($1 (%108 $0))))) ((%18 (%60
       (\%149. ($1 (%109 $0))))) ($0 %110)))) (%97 (\%98. ($1 $0))))))`)
  end
  val _ = DB.bindl "parserDef"
  [("item_TY_DEF",item_TY_DEF,DB.Def), ("item_repfns",item_repfns,DB.Def),
   ("parserDef0_def",parserDef0_def,DB.Def), ("item",item,DB.Def),
   ("item_case_def",item_case_def,DB.Def),
   ("item_size_def",item_size_def,DB.Def),
   ("state_TY_DEF",state_TY_DEF,DB.Def),
   ("state_repfns",state_repfns,DB.Def),
   ("parserDef1_def",parserDef1_def,DB.Def), ("state",state,DB.Def),
   ("state_case_def",state_case_def,DB.Def),
   ("state_size_def",state_size_def,DB.Def),
   ("action_TY_DEF",action_TY_DEF,DB.Def),
   ("action_repfns",action_repfns,DB.Def),
   ("parserDef2_def",parserDef2_def,DB.Def),
   ("parserDef3_def",parserDef3_def,DB.Def),
   ("parserDef4_def",parserDef4_def,DB.Def), ("REDUCE",REDUCE,DB.Def),
   ("GOTO",GOTO,DB.Def), ("NA",NA,DB.Def),
   ("action_case_def",action_case_def,DB.Def),
   ("action_size_def",action_size_def,DB.Def),
   ("stateSym_def",stateSym_def,DB.Def),
   ("stateItl_def",stateItl_def,DB.Def),
   ("datatype_item",datatype_item,DB.Thm), ("item_11",item_11,DB.Thm),
   ("item_case_cong",item_case_cong,DB.Thm),
   ("item_nchotomy",item_nchotomy,DB.Thm),
   ("item_Axiom",item_Axiom,DB.Thm),
   ("item_induction",item_induction,DB.Thm),
   ("datatype_state",datatype_state,DB.Thm), ("state_11",state_11,DB.Thm),
   ("state_case_cong",state_case_cong,DB.Thm),
   ("state_nchotomy",state_nchotomy,DB.Thm),
   ("state_Axiom",state_Axiom,DB.Thm),
   ("state_induction",state_induction,DB.Thm),
   ("datatype_action",datatype_action,DB.Thm),
   ("action_11",action_11,DB.Thm),
   ("action_distinct",action_distinct,DB.Thm),
   ("action_case_cong",action_case_cong,DB.Thm),
   ("action_nchotomy",action_nchotomy,DB.Thm),
   ("action_Axiom",action_Axiom,DB.Thm),
   ("action_induction",action_induction,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("parseTreeTheory.parseTree_grammars",
                          parseTreeTheory.parseTree_grammars),
                         ("whileLemmasTheory.whileLemmas_grammars",
                          whileLemmasTheory.whileLemmas_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms temp_add_type "item"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_item")
        {Name = "dest_item", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_item")
        {Name = "mk_item", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parserDef0")
        {Name = "parserDef0", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "item")
        {Name = "item", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "item_case")
        {Name = "item_case", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "item_size")
        {Name = "item_size", Thy = "parserDef"}
  val _ = update_grms temp_add_type "state"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_state")
        {Name = "dest_state", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_state")
        {Name = "mk_state", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parserDef1")
        {Name = "parserDef1", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "state")
        {Name = "state", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "state_case")
        {Name = "state_case", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "state_size")
        {Name = "state_size", Thy = "parserDef"}
  val _ = update_grms temp_add_type "action"
  val _ = update_grms
       (temp_overload_on_by_nametype "dest_action")
        {Name = "dest_action", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mk_action")
        {Name = "mk_action", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parserDef2")
        {Name = "parserDef2", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parserDef3")
        {Name = "parserDef3", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "parserDef4")
        {Name = "parserDef4", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "REDUCE")
        {Name = "REDUCE", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "GOTO")
        {Name = "GOTO", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "NA")
        {Name = "NA", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "action_case")
        {Name = "action_case", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "action_size")
        {Name = "action_size", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "stateSym")
        {Name = "stateSym", Thy = "parserDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "stateItl")
        {Name = "stateItl", Thy = "parserDef"}
  val parserDef_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG item_Axiom,
           case_def=item_case_def,
           case_cong=item_case_cong,
           induction=ORIG item_induction,
           nchotomy=item_nchotomy,
           size=SOME(Parse.Term`(parserDef$item_size) :(parserDef$item) -> (num$num)`,
                     ORIG item_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME item_11,
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
          {ax=ORIG state_Axiom,
           case_def=state_case_def,
           case_cong=state_case_cong,
           induction=ORIG state_induction,
           nchotomy=state_nchotomy,
           size=SOME(Parse.Term`(parserDef$state_size) :(parserDef$state) -> (num$num)`,
                     ORIG state_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME state_11,
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
          {ax=ORIG action_Axiom,
           case_def=action_case_def,
           case_cong=action_case_cong,
           induction=ORIG action_induction,
           nchotomy=action_nchotomy,
           size=SOME(Parse.Term`(parserDef$action_size) :(parserDef$action) -> (num$num)`,
                     ORIG action_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME action_11,
           distinct=SOME action_distinct,
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
  
  
  val _ = computeLib.add_funs [stateSym_def];  
  
  val _ = computeLib.add_funs [stateItl_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
