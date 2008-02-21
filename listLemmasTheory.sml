structure listLemmasTheory :> listLemmasTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading listLemmasTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open containerLemmasTheory stringTheory
  in end;
  val _ = Theory.link_parents
          ("listLemmas",
          Arbnum.fromString "1203550994",
          Arbnum.fromString "402807")
          [("containerLemmas",
           Arbnum.fromString "1203550984",
           Arbnum.fromString "18625"),
           ("string",
           Arbnum.fromString "1201303028",
           Arbnum.fromString "222060")];
  val _ = Theory.incorporate_types "listLemmas" [];
  val _ = Theory.incorporate_consts "listLemmas"
     [("push",
       ((T"list" "list" [alpha] --> (alpha --> T"list" "list" [alpha])))),
      ("take",
       ((T"num" "num" [] -->
         (T"list" "list" [alpha] -->
          T"option" "option" [T"list" "list" [alpha]])))),
      ("delete",
       ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
      ("breakAtElem",
       ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
      ("diff",
       ((T"list" "list" [alpha] -->
         (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
      ("diff_tupled",
       ((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]]
         --> T"list" "list" [alpha]))),
      ("pop",
       ((T"list" "list" [alpha] -->
         (T"num" "num" [] --> T"list" "list" [alpha])))),
      ("take1_defn_tupled",
       ((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
         T"list" "list" [alpha]))),
      ("take1",
       ((T"num" "num" [] -->
         (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
      ("rmDupes",((T"list" "list" [alpha] --> T"list" "list" [alpha])))];
  
  local
  val share_table = Vector.fromList
  [C"/\\" "bool" ((bool --> (bool --> bool))),
   C"!" "bool" (((alpha --> bool) --> bool)), V"x" (alpha),
   C"=" "min"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"delete" "listLemmas"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"NIL" "list" (T"list" "list" [alpha]), V"l" (alpha),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"ls" (T"list" "list" [alpha]),
   C"CONS" "list"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [alpha] -->
       (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"=" "min"
    (((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
       T"list" "list" [alpha]) -->
      ((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
        T"list" "list" [alpha]) --> bool))),
   C"diff_tupled" "listLemmas"
    ((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
      T"list" "list" [alpha])),
   C"WFREC" "relation"
    (((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
       (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
        bool)) -->
      (((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]]
         --> T"list" "list" [alpha]) -->
        (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]]
         --> T"list" "list" [alpha])) -->
       (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
        T"list" "list" [alpha])))),
   C"@" "min"
    ((((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
        (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]]
         --> bool)) --> bool) -->
      (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
       (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
        bool)))),
   V"R"
    ((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
      (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
       bool))),
   C"WF" "relation"
    (((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
       (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
        bool)) --> bool)), V"v5" (T"list" "list" [alpha]), V"v4" (alpha),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool))),
   C"," "pair"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] -->
       T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]]))),
   V"diff_tupled"
    ((T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
      T"list" "list" [alpha])),
   V"a" (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]]),
   C"pair_case" "pair"
    (((T"list" "list" [alpha] -->
       (T"list" "list" [alpha] --> T"list" "list" [alpha])) -->
      (T"prod" "pair" [T"list" "list" [alpha], T"list" "list" [alpha]] -->
       T"list" "list" [alpha]))), V"v" (T"list" "list" [alpha]),
   V"v1" (T"list" "list" [alpha]),
   C"list_case" "list"
    ((T"list" "list" [alpha] -->
      ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha])) -->
       (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
   C"I" "combin" ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   V"v10" (alpha), V"v11" (T"list" "list" [alpha]), V"v6" (alpha),
   V"v7" (T"list" "list" [alpha]), V"v12" (alpha),
   V"v13" (T"list" "list" [alpha]), V"x" (T"list" "list" [alpha]),
   V"x1" (T"list" "list" [alpha]),
   C"diff" "listLemmas"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"=" "min"
    (((T"list" "list" [alpha] --> T"list" "list" [alpha]) -->
      ((T"list" "list" [alpha] --> T"list" "list" [alpha]) --> bool))),
   C"rmDupes" "listLemmas"
    ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   C"WFREC" "relation"
    (((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool)) -->
      (((T"list" "list" [alpha] --> T"list" "list" [alpha]) -->
        (T"list" "list" [alpha] --> T"list" "list" [alpha])) -->
       (T"list" "list" [alpha] --> T"list" "list" [alpha])))),
   C"@" "min"
    ((((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool)) -->
       bool) -->
      (T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool)))),
   V"R" ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"WF" "relation"
    (((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool)) -->
      bool)), V"t" (T"list" "list" [alpha]), V"h" (alpha),
   V"rmDupes" ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   V"a" (T"list" "list" [alpha]), V"e" (alpha),
   C"breakAtElem" "listLemmas"
    ((alpha --> (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   V"l" (T"list" "list" [alpha]),
   C"push" "listLemmas"
    ((T"list" "list" [alpha] --> (alpha --> T"list" "list" [alpha]))),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"v0" (T"num" "num" []),
   C"pop" "listLemmas"
    ((T"list" "list" [alpha] -->
      (T"num" "num" [] --> T"list" "list" [alpha]))),
   V"num" (T"num" "num" []),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"0" "num" (T"num" "num" []),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"NUMERAL" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"BIT1" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   C"ZERO" "arithmetic" (T"num" "num" []),
   C"=" "min"
    (((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
       T"list" "list" [alpha]) -->
      ((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
        T"list" "list" [alpha]) --> bool))),
   C"take1_defn_tupled" "listLemmas"
    ((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
      T"list" "list" [alpha])),
   C"WFREC" "relation"
    (((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
       (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] --> bool))
      -->
      (((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
         T"list" "list" [alpha]) -->
        (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
         T"list" "list" [alpha])) -->
       (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
        T"list" "list" [alpha])))),
   C"@" "min"
    ((((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
        (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
         bool)) --> bool) -->
      (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
       (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
        bool)))),
   V"R"
    ((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
      (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
       bool))),
   C"WF" "relation"
    (((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
       (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] --> bool))
      --> bool)), V"xs" (T"list" "list" [alpha]), V"v2" (T"num" "num" []),
   C"SUC" "num" ((T"num" "num" [] --> T"num" "num" [])),
   C"," "pair"
    ((T"num" "num" [] -->
      (T"list" "list" [alpha] -->
       T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]]))),
   C"T" "bool" (bool),
   V"take1_defn_tupled"
    ((T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
      T"list" "list" [alpha])),
   V"a" (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]]),
   C"pair_case" "pair"
    (((T"num" "num" [] -->
       (T"list" "list" [alpha] --> T"list" "list" [alpha])) -->
      (T"prod" "pair" [T"num" "num" [], T"list" "list" [alpha]] -->
       T"list" "list" [alpha]))), V"v" (T"num" "num" []),
   C"num_case" "arithmetic"
    ((T"list" "list" [alpha] -->
      ((T"num" "num" [] --> T"list" "list" [alpha]) -->
       (T"num" "num" [] --> T"list" "list" [alpha])))),
   V"v3" (T"num" "num" []), C"ARB" "bool" (T"list" "list" [alpha]),
   V"x" (T"num" "num" []),
   C"take1" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   V"n" (T"num" "num" []),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [alpha]] -->
      (T"option" "option" [T"list" "list" [alpha]] --> bool))),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [alpha] -->
       T"option" "option" [T"list" "list" [alpha]]))),
   C"COND" "bool"
    ((bool -->
      (T"option" "option" [T"list" "list" [alpha]] -->
       (T"option" "option" [T"list" "list" [alpha]] -->
        T"option" "option" [T"list" "list" [alpha]])))),
   C">=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"LENGTH" "list" ((T"list" "list" [alpha] --> T"num" "num" [])),
   C"SOME" "option"
    ((T"list" "list" [alpha] -->
      T"option" "option" [T"list" "list" [alpha]])),
   C"NONE" "option" (T"option" "option" [T"list" "list" [alpha]]),
   V"r" (T"list" "list" [alpha]), C"=" "min" ((bool --> (bool --> bool))),
   C"NULL" "list" ((T"list" "list" [alpha] --> bool)),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"p" ((alpha --> bool)),
   C">" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"FILTER" "list"
    (((alpha --> bool) -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"?" "bool" (((alpha --> bool) --> bool)),
   C"?" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"f" ((alpha --> bool)),
   C"APPEND" "list"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   V"l1" (T"list" "list" [alpha]), V"l2" (T"list" "list" [alpha]),
   V"y" (alpha), V"sym" (alpha), V"r1" (T"list" "list" [alpha]),
   V"r2" (T"list" "list" [alpha]), V"v'" (T"list" "list" [alpha]),
   V"s1" (T"list" "list" [alpha]), V"s2" (T"list" "list" [alpha]),
   V"rhs" (T"list" "list" [alpha]), V"s1'" (T"list" "list" [alpha]),
   V"s2'" (T"list" "list" [alpha]),
   C"\\/" "bool" ((bool --> (bool --> bool))),
   C"BIT2" "arithmetic" ((T"num" "num" [] --> T"num" "num" [])),
   V"e1" (alpha), V"e2" (alpha), V"e3" (alpha),
   C"<=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"h'" (alpha), V"r'" (T"list" "list" [alpha]),
   V"p" (T"list" "list" [alpha]), V"s" (T"list" "list" [alpha]),
   C"!" "bool" (((beta --> bool) --> bool)), V"x" (beta),
   V"NTS" ((gamma --> alpha)), V"t1" (gamma),
   C"!" "bool" (((T"list" "list" [beta] --> bool) --> bool)),
   V"s" (T"list" "list" [beta]),
   C"+" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C"LENGTH" "list" ((T"list" "list" [beta] --> T"num" "num" [])),
   C"NULL" "list" ((T"list" "list" [beta] --> bool)), V"t1" (beta),
   V"t2" (beta), V"NTS" ((beta --> alpha)),
   C"FINITE" "pred_set" (((alpha --> bool) --> bool)),
   C"LIST_TO_SET" "list" ((T"list" "list" [alpha] --> (alpha --> bool))),
   C"!" "bool"
    ((((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool)) -->
       bool) --> bool)),
   V"P" ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   V"v2" (alpha), V"v3" (T"list" "list" [alpha]), V"v8" (alpha),
   V"v9" (T"list" "list" [alpha]),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"el" (alpha),
   C"!" "bool" ((((T"list" "list" [alpha] --> bool) --> bool) --> bool)),
   V"P" ((T"list" "list" [alpha] --> bool)),
   C"=" "min" (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"INSERT" "pred_set"
    ((alpha --> ((alpha --> bool) --> (alpha --> bool)))),
   C"CARD" "pred_set" (((alpha --> bool) --> T"num" "num" [])),
   V"l2" (T"list" "list" [beta]),
   C"CARD" "pred_set" (((beta --> bool) --> T"num" "num" [])),
   C"LIST_TO_SET" "list" ((T"list" "list" [beta] --> (beta --> bool))),
   V"s1" ((alpha --> bool)), V"s2" ((alpha --> bool)),
   C"SUBSET" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"REVERSE" "list" ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   C"!" "bool"
    (((T"list" "list" [T"list" "list" [alpha]] --> bool) --> bool)),
   V"x" (T"list" "list" [T"list" "list" [alpha]]),
   V"y" (T"list" "list" [T"list" "list" [alpha]]),
   C"FLAT" "list"
    ((T"list" "list" [T"list" "list" [alpha]] --> T"list" "list" [alpha])),
   C"APPEND" "list"
    ((T"list" "list" [T"list" "list" [alpha]] -->
      (T"list" "list" [T"list" "list" [alpha]] -->
       T"list" "list" [T"list" "list" [alpha]]))),
   V"l" (T"list" "list" [beta]),
   C"MAP" "list"
    (((beta --> T"list" "list" [alpha]) -->
      (T"list" "list" [beta] -->
       T"list" "list" [T"list" "list" [alpha]]))),
   V"f" ((beta --> T"list" "list" [alpha])),
   V"e'" (T"list" "list" [alpha]),
   C"MEM" "list"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [T"list" "list" [alpha]] --> bool))),
   V"pfx" (T"list" "list" [alpha]), V"sfx" (T"list" "list" [alpha]),
   V"a" (alpha),
   C"!" "bool"
    ((((T"num" "num" [] --> (T"list" "list" [alpha] --> bool)) --> bool)
      --> bool)),
   V"P" ((T"num" "num" [] --> (T"list" "list" [alpha] --> bool))),
   C"!" "bool" ((((alpha --> beta) --> bool) --> bool)),
   V"f" ((alpha --> beta)),
   C"!" "bool" ((((gamma --> alpha) --> bool) --> bool)),
   V"g" ((gamma --> alpha)),
   C"!" "bool" (((T"list" "list" [gamma] --> bool) --> bool)),
   V"l" (T"list" "list" [gamma]),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [beta]] -->
      (T"option" "option" [T"list" "list" [beta]] --> bool))),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [beta] -->
       T"option" "option" [T"list" "list" [beta]]))),
   C"MAP" "list"
    (((gamma --> beta) -->
      (T"list" "list" [gamma] --> T"list" "list" [beta]))),
   C"o" "combin"
    (((alpha --> beta) --> ((gamma --> alpha) --> (gamma --> beta)))),
   C"SOME" "option"
    ((T"list" "list" [beta] -->
      T"option" "option" [T"list" "list" [beta]])),
   V"x" (T"list" "list" [beta]), V"x'" (T"list" "list" [alpha]),
   C"MAP" "list"
    (((gamma --> alpha) -->
      (T"list" "list" [gamma] --> T"list" "list" [alpha]))),
   C"=" "min"
    ((T"list" "list" [beta] --> (T"list" "list" [beta] --> bool))),
   C"take1" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [beta] --> T"list" "list" [beta]))),
   C"MAP" "list"
    (((alpha --> beta) -->
      (T"list" "list" [alpha] --> T"list" "list" [beta]))),
   C"REVERSE" "list" ((T"list" "list" [beta] --> T"list" "list" [beta])),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [beta]] -->
      T"list" "list" [beta])),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [alpha]] -->
      T"list" "list" [alpha])), V"rst" (T"list" "list" [alpha]),
   V"y" (T"list" "list" [alpha]),
   C"!" "bool"
    (((T"list" "list" [T"prod" "pair" [alpha, beta]] --> bool) --> bool)),
   V"stl" (T"list" "list" [T"prod" "pair" [alpha, beta]]),
   C"=" "min"
    ((T"option" "option" [T"list" "list" [T"prod" "pair" [alpha, beta]]]
      -->
      (T"option" "option" [T"list" "list" [T"prod" "pair" [alpha, beta]]]
       --> bool))),
   C"take" "listLemmas"
    ((T"num" "num" [] -->
      (T"list" "list" [T"prod" "pair" [alpha, beta]] -->
       T"option" "option"
        [T"list" "list" [T"prod" "pair" [alpha, beta]]]))),
   C"LENGTH" "list" ((T"list" "list" [gamma] --> T"num" "num" [])),
   V"r" (T"list" "list" [gamma]),
   C"SOME" "option"
    ((T"list" "list" [T"prod" "pair" [alpha, beta]] -->
      T"option" "option" [T"list" "list" [T"prod" "pair" [alpha, beta]]])),
   V"x" (T"list" "list" [T"prod" "pair" [alpha, beta]]),
   C"MAP" "list"
    (((T"prod" "pair" [alpha, beta] --> beta) -->
      (T"list" "list" [T"prod" "pair" [alpha, beta]] -->
       T"list" "list" [beta]))),
   C"SND" "pair" ((T"prod" "pair" [alpha, beta] --> beta)),
   C"THE" "option"
    ((T"option" "option" [T"list" "list" [T"prod" "pair" [alpha, beta]]]
      --> T"list" "list" [T"prod" "pair" [alpha, beta]])),
   C"?" "bool" (((T"list" "list" [beta] --> bool) --> bool)),
   V"x'" (T"list" "list" [beta]),
   C"pop" "listLemmas"
    ((T"list" "list" [beta] -->
      (T"num" "num" [] --> T"list" "list" [beta]))),
   V"l'" (T"list" "list" [alpha]), V"l1'" (T"list" "list" [alpha]),
   V"l2'" (T"list" "list" [alpha]), V"e'" (alpha), V"P" ((alpha --> bool)),
   C"EVERY" "list"
    (((alpha --> bool) --> (T"list" "list" [alpha] --> bool))),
   C"ALL_DISTINCT" "list" ((T"list" "list" [alpha] --> bool)),
   C"DIFF" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> (alpha --> bool))))]
  val DT = Thm.disk_thm share_table
  in
  val delete_def =
    DT(["DISK_THM"], [],
       `((%0 (%1 (\%2. ((%3 ((%4 $0) %5)) %5)))) (%1 (\%2. (%1 (\%6. (%7
       (\%8. ((%3 ((%4 $2) ((%9 $1) $0))) (((%10 ((%11 $2) $1)) ((%4 $2)
       $0)) ((%9 $1) ((%4 $2) $0)))))))))))`)
  val diff_tupled_primitive_def =
    DT([], [],
       `((%12 %13) ((%14 (%15 (\%16. ((%0 (%17 $0)) ((%0 (%7 (\%8. (%7
       (\%18. (%1 (\%19. (%1 (\%6. ((%20 (%21 ((%22 $0) ((%9 $1) $2))))
       (($4 ((%23 ((%9 $1) $2)) $3)) ((%23 ((%9 $1) $2)) ((%9 $0)
       $3))))))))))))) (%7 (\%8. (%7 (\%18. (%1 (\%19. (%1 (\%6. ((%20
       ((%22 $0) ((%9 $1) $2))) (($4 ((%23 ((%4 $0) ((%9 $1) $2))) $3))
       ((%23 ((%9 $1) $2)) ((%9 $0) $3))))))))))))))))) (\%24. (\%25. ((%26
       (\%27. (\%28. (((%29 (((%29 (%30 %5)) (\%31. (\%32. (%30 %5)))) $0))
       (\%33. (\%34. (((%29 (%30 ((%9 $1) $0))) (\%35. (\%36. (%30 (((%10
       ((%22 $1) ((%9 $3) $2))) ($7 ((%23 ((%4 $1) ((%9 $3) $2))) $0))) ($7
       ((%23 ((%9 $3) $2)) $0))))))) $2)))) $1)))) $0)))))`)
  val diff_curried_def =
    DT([], [],
       `(%7 (\%37. (%7 (\%38. ((%3 ((%39 $1) $0)) (%13 ((%23 $1)
       $0)))))))`)
  val rmDupes_defn_primitive_def =
    DT([], [],
       `((%40 %41) ((%42 (%43 (\%44. ((%0 (%45 $0)) (%7 (\%46. (%1 (\%47.
       (($2 ((%4 $0) $1)) ((%9 $0) $1)))))))))) (\%48. (\%49. (((%29 (%30
       %5)) (\%47. (\%46. (%30 ((%9 $1) ($3 ((%4 $1) $0))))))) $0)))))`)
  val breakAtElem_def =
    DT(["DISK_THM"], [],
       `((%0 (%1 (\%50. ((%3 ((%51 $0) %5)) %5)))) (%1 (\%50. (%1 (\%6. (%7
       (\%8. ((%3 ((%51 $2) ((%9 $1) $0))) (((%10 ((%11 $2) $1)) $0) ((%51
       $2) $0))))))))))`)
  val push_def =
    DT([], [],
       `(%7 (\%52. (%1 (\%50. ((%3 ((%53 $1) $0)) ((%9 $0) $1))))))`)
  val pop_def =
    DT(["DISK_THM"], [],
       `((%0 (%54 (\%55. ((%3 ((%56 %5) $0)) %5)))) (%1 (\%47. (%7 (\%46.
       (%54 (\%57. ((%3 ((%56 ((%9 $2) $1)) $0)) (((%10 ((%58 $0) %59))
       ((%9 $2) $1)) ((%56 $1) ((%60 $0) (%61 (%62 %63)))))))))))))`)
  val take1_defn_tupled_primitive_def =
    DT([], [],
       `((%64 %65) ((%66 (%67 (\%68. ((%0 (%69 $0)) ((%0 (%1 (\%2. (%7
       (\%70. (%54 (\%71. ((%20 (%21 ((%58 (%72 $0)) %59))) (($3 ((%73
       ((%60 (%72 $0)) (%61 (%62 %63)))) $1)) ((%73 (%72 $0)) ((%9 $2)
       $1))))))))))) (%1 (\%2. (%7 (\%70. ((%20 (%21 %74)) (($2 ((%73 ((%60
       %59) (%61 (%62 %63)))) $0)) ((%73 %59) ((%9 $1) $0)))))))))))))
       (\%75. (\%76. ((%77 (\%78. (\%28. (((%79 (((%29 (%30 %5)) (\%19.
       (\%18. (%30 (((%10 ((%58 %59) %59)) %5) ((%9 $1) ($5 ((%73 ((%60
       %59) (%61 (%62 %63)))) $0)))))))) $0)) (\%80. (((%29 %81) (\%33.
       (\%34. (%30 (((%10 ((%58 (%72 $2)) %59)) %5) ((%9 $1) ($6 ((%73
       ((%60 (%72 $2)) (%61 (%62 %63)))) $0)))))))) $1))) $1)))) $0)))))`)
  val take1_defn_curried_def =
    DT([], [],
       `(%54 (\%82. (%7 (\%38. ((%3 ((%83 $1) $0)) (%65 ((%73 $1)
       $0)))))))`)
  val take_def =
    DT([], [],
       `(%54 (\%84. (%7 (\%52. ((%85 ((%86 $1) $0)) (((%87 ((%88 (%89 $0))
       $1)) (%90 ((%83 $1) $0))) %91))))))`)
  val list_l1 =
    DT(["DISK_THM"], [], `(%7 (\%92. ((%93 ((%3 $0) %5)) (%94 $0))))`)
  val filter_l1 =
    DT(["DISK_THM"], [],
       `(%95 (\%96. (%7 (\%52. ((%20 ((%97 (%89 ((%98 $1) $0))) %59)) (%99
       (\%50. ((%0 ((%22 $0) $1)) ($2 $0)))))))))`)
  val len_not_0 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 (%21 ((%58 (%89 $0)) %59))) (%99 (\%47. (%100
       (\%46. ((%3 $2) ((%9 $1) $0)))))))))`)
  val filter_l2 =
    DT(["DISK_THM"], [],
       `(%95 (\%101. (%7 (\%52. ((%93 ((%58 (%89 ((%98 $1) $0))) %59)) (%21
       (%99 (\%50. ((%0 ((%22 $0) $1)) ($2 $0))))))))))`)
  val lres =
    DT(["DISK_THM"], [],
       `((%20 ((%3 ((%102 ((%102 %103) ((%9 %2) %5))) %104)) ((%9 %105)
       %5))) ((%0 ((%3 %103) %5)) ((%0 ((%3 %104) %5)) ((%11 %2) %105))))`)
  val lresb =
    DT(["DISK_THM"], [],
       `((%20 ((%0 ((%3 %103) %5)) ((%0 ((%3 %104) %5)) ((%11 %2) %105))))
       ((%3 ((%102 ((%102 %103) ((%9 %2) %5))) %104)) ((%9 %105) %5)))`)
  val lreseq =
    DT(["DISK_THM"], [],
       `((%93 ((%3 ((%102 ((%102 %103) ((%9 %2) %5))) %104)) ((%9 %105)
       %5))) ((%0 ((%3 %103) %5)) ((%0 ((%3 %104) %5)) ((%11 %2) %105))))`)
  val rgr_r9 =
    DT(["DISK_THM"], [],
       `(%7 (\%92. ((%20 ((%22 %106) $0)) (%100 (\%107. (%100 (\%108. ((%3
       $2) ((%102 ((%102 $1) ((%9 %106) %5))) $0)))))))))`)
  val rgr_r9b =
    DT(["DISK_THM"], [],
       `(%7 (\%92. ((%20 (%100 (\%107. (%100 (\%108. ((%3 $2) ((%102 ((%102
       $1) ((%9 %106) %5))) $0))))))) ((%22 %106) $0))))`)
  val rgr_r9eq =
    DT(["DISK_THM"], [],
       `(%7 (\%92. ((%93 ((%22 %106) $0)) (%100 (\%107. (%100 (\%108. ((%3
       $2) ((%102 ((%102 $1) ((%9 %106) %5))) $0)))))))))`)
  val list_r1 =
    DT(["DISK_THM"], [],
       `(%7 (\%27. (%7 (\%109. (%1 (\%2. ((%20 ((%3 $2) ((%102 $1) ((%9 $0)
       %5)))) ((%22 $0) $2))))))))`)
  val list_r2 =
    DT(["DISK_THM"], [],
       `(%7 (\%110. (%7 (\%111. (%7 (\%112. (%1 (\%2. ((%20 ((%3 ((%102
       ((%102 $3) $1)) $2)) ((%9 $0) %5))) ((%20 (%21 ((%3 $1) %5))) ((%0
       ((%3 $3) %5)) ((%3 $2) %5))))))))))))`)
  val list_r6 =
    DT(["DISK_THM"], [],
       `(%7 (\%110. (%7 (\%111. (%7 (\%113. (%7 (\%114. (%1 (\%2. ((%20
       ((%3 ((%102 ((%102 $2) ((%9 $0) %5))) $1)) ((%102 $4) $3))) (%100
       (\%103. (%100 (\%104. ((%115 ((%0 ((%3 $6) ((%102 ((%102 $4) ((%9
       $2) %5))) $1))) ((%0 ((%3 $5) $0)) ((%3 $3) ((%102 $1) $0))))) ((%0
       ((%3 $5) ((%102 ((%102 $0) ((%9 $2) %5))) $3))) ((%0 ((%3 $6) $1))
       ((%3 $4) ((%102 $1) $0))))))))))))))))))))`)
  val list_lem1 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 ((%58 (%89 $0)) (%61 (%62 %63)))) (%99 (\%50. ((%3
       $1) ((%9 $0) %5)))))))`)
  val list_lem2 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 ((%58 (%89 $0)) (%61 (%116 %63)))) (%99 (\%117.
       (%99 (\%118. ((%3 $2) ((%9 $1) ((%9 $0) %5))))))))))`)
  val list_lem3 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 ((%88 (%89 $0)) (%61 (%62 (%62 %63))))) (%99
       (\%117. (%99 (\%118. (%99 (\%119. (%100 (\%92. ((%3 $4) ((%102 ((%9
       $3) ((%9 $2) ((%9 $1) %5)))) $0)))))))))))))`)
  val list_lem4 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 ((%88 (%89 $0)) (%61 (%116 %63)))) (%99 (\%117.
       (%99 (\%118. (%100 (\%92. ((%3 $3) ((%102 ((%9 $2) ((%9 $1) %5)))
       $0)))))))))))`)
  val l_lemma1 =
    DT(["DISK_THM"], [],
       `(%7 (\%92. ((%20 ((%120 (%61 (%62 %63))) (%89 $0))) (%99 (\%121.
       (%100 (\%122. ((%3 $2) ((%9 $1) $0)))))))))`)
  val sl =
    DT(["DISK_THM"], [],
       `(%7 (\%123. (%7 (\%124. (%1 (\%2. ((%20 ((%88 (%89 ((%102 ((%102
       $2) ((%9 $0) %5))) $1))) (%61 (%62 (%62 %63))))) ((%115 (%21 (%94
       $1))) (%21 (%94 $2))))))))))`)
  val sl_l2 =
    DT(["DISK_THM"], [],
       `(%7 (\%123. (%7 (\%124. (%125 (\%126. ((%20 ((%88 (%89 ((%102
       ((%102 $2) ((%9 (%127 %128)) %5))) $1))) (%61 (%116 %63)))) ((%115
       (%21 (%94 $1))) (%21 (%94 $2))))))))))`)
  val sl_l3 =
    DT(["DISK_THM"], [],
       `(%7 (\%123. (%129 (\%130. ((%20 ((%88 ((%131 (%89 $1)) (%132 $0)))
       (%61 (%62 %63)))) ((%115 (%21 (%133 $0))) (%21 (%94 $1))))))))`)
  val len0 =
    DT(["DISK_THM"], [],
       `(%7 (\%124. ((%93 (%94 $0)) ((%58 (%89 $0)) %59))))`)
  val notLen1 =
    DT(["DISK_THM"], [],
       `(%7 (\%123. (%7 (\%124. ((%20 ((%115 (%21 (%94 $1))) (%21 (%94
       $0)))) (%1 (\%2. (%21 ((%120 (%89 ((%102 ((%102 $2) ((%9 $0) %5)))
       $1))) (%61 (%62 %63)))))))))))`)
  val listNotNull =
    DT(["DISK_THM"], [],
       `(%7 (\%123. ((%93 (%21 (%94 $0))) (%99 (\%47. (%100 (\%46. ((%3 $2)
       ((%9 $1) $0)))))))))`)
  val sl_l4 =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%125 (\%134. (%125 (\%135. (%7 (\%123. (%7 (\%124. (%21
       ((%3 ((%9 $4) %5)) ((%102 ((%102 $1) ((%9 (%136 $3)) ((%9 (%136 $2))
       %5)))) $0)))))))))))))`)
  val sl_l5 =
    DT(["DISK_THM"], [],
       `(%1 (\%117. (%1 (\%118. (%125 (\%134. (%125 (\%135. (%7 (\%123. (%7
       (\%124. ((%20 ((%3 ((%9 $5) ((%9 $4) %5))) ((%102 ((%102 $1) ((%9
       (%136 $3)) ((%9 (%136 $2)) %5)))) $0))) ((%0 (%94 $1)) (%94
       $0)))))))))))))))`)
  val finiteLists = DT(["DISK_THM"], [], `(%7 (\%52. (%137 (%138 $0))))`)
  val diff_ind =
    DT(["DISK_THM"], [],
       `(%139 (\%140. ((%20 ((%0 (%1 (\%141. (%7 (\%142. (($2 ((%9 $1) $0))
       %5)))))) ((%0 (($0 %5) %5)) ((%0 (%1 (\%143. (%7 (\%144. (($2 %5)
       ((%9 $1) $0))))))) (%1 (\%19. (%7 (\%18. (%1 (\%6. (%7 (\%8. ((%20
       ((%0 ((%20 (%21 ((%22 $1) ((%9 $3) $2)))) (($4 ((%9 $3) $2)) $0)))
       ((%20 ((%22 $1) ((%9 $3) $2))) (($4 ((%4 $1) ((%9 $3) $2))) $0))))
       (($4 ((%9 $3) $2)) ((%9 $1) $0))))))))))))))) (%7 (\%27. (%7 (\%28.
       (($2 $1) $0))))))))`)
  val diff_def =
    DT(["DISK_THM"], [],
       `((%0 ((%3 ((%39 ((%9 %141) %142)) %5)) ((%9 %141) %142))) ((%0 ((%3
       ((%39 %5) %5)) %5)) ((%0 ((%3 ((%39 %5) ((%9 %143) %144))) %5)) ((%3
       ((%39 ((%9 %19) %18)) ((%9 %6) %8))) (((%10 ((%22 %6) ((%9 %19)
       %18))) ((%39 ((%4 %6) ((%9 %19) %18))) %8)) ((%39 ((%9 %19) %18))
       %8))))))`)
  val delete_not_mem1 =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. ((%20 (%21 ((%22 $1) $0))) ((%3 ((%4 $1) $0))
       $0))))))`)
  val delete_append =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%103. (%7 (\%104. ((%3 ((%4 $2) ((%102 $1) $0)))
       ((%102 ((%4 $2) $1)) ((%4 $2) $0)))))))))`)
  val not_mem_delete =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. (%21 ((%22 $1) ((%4 $1) $0)))))))`)
  val delete_not_mem2 =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. ((%20 ((%3 ((%4 $1) $0)) $0)) (%21 ((%22 $1)
       $0)))))))`)
  val delete_not_mem =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. ((%93 ((%3 ((%4 $1) $0)) $0)) (%21 ((%22 $1)
       $0)))))))`)
  val delete_mem_len =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. ((%20 ((%22 $1) $0)) ((%145 (%89 ((%4 $1)
       $0))) (%89 $0)))))))`)
  val delete_nil =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. ((%93 ((%3 ((%4 $1) $0)) %5)) ((%115 ((%3 $0)
       %5)) (%1 (\%146. ((%20 ((%22 $0) $1)) ((%11 $0) $2))))))))))`)
  val delete_mem_list =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%1 (\%47. (%7 (\%52. ((%20 (%21 ((%11 $1) $2))) ((%93
       ((%22 $2) $0)) ((%22 $2) ((%4 $1) $0))))))))))`)
  val delete_twice =
    DT(["DISK_THM"], [],
       `(%1 (\%47. (%7 (\%52. ((%3 ((%4 $1) $0)) ((%4 $1) ((%4 $1)
       $0)))))))`)
  val delete_diff_elem =
    DT(["DISK_THM"], [],
       `(%1 (\%47. (%1 (\%121. (%7 (\%52. ((%3 ((%4 $2) ((%4 $1) $0))) ((%4
       $1) ((%4 $2) $0)))))))))`)
  val rmDupes =
    DT(["DISK_THM"], [],
       `((%0 ((%3 (%41 %5)) %5)) ((%3 (%41 ((%9 %47) %46))) ((%9 %47) (%41
       ((%4 %47) %46)))))`)
  val rmDupes_ind =
    DT(["DISK_THM"], [],
       `(%147 (\%148. ((%20 ((%0 ($0 %5)) (%1 (\%47. (%7 (\%46. ((%20 ($2
       ((%4 $1) $0))) ($2 ((%9 $1) $0))))))))) (%7 (\%27. ($1 $0))))))`)
  val rmd_r2_1 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%22 %50) $0)) ((%22 %50) (%41 $0)))))`)
  val rmd_r2_2 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%22 %50) (%41 $0))) ((%22 %50) $0))))`)
  val rmd_r2 =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. ((%93 ((%22 $1) $0)) ((%22 $1) (%41
       $0)))))))`)
  val rmDupes_not_nil =
    DT(["DISK_THM"], [],
       `(%1 (\%2. (%7 (\%70. (%21 ((%3 (%41 ((%9 $1) $0))) %5))))))`)
  val rmd_mem_list1 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%22 %50) $0)) ((%22 %50) (%41 $0)))))`)
  val rmd_mem_list2 =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%22 %50) (%41 $0))) ((%22 %50) $0))))`)
  val rmd_mem_list =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 ((%22 %50) (%41 $0))) ((%22 %50) $0))))`)
  val rmDupes_len =
    DT(["DISK_THM"], [], `(%7 (\%52. ((%88 (%89 $0)) (%89 (%41 $0)))))`)
  val rmd_del =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%3 (%41 ((%4 %47) $0))) ((%4 %47) (%41 $0)))))`)
  val rmda_del_rmda =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%3 (%41 ((%4 %47) $0))) (%41 ((%4 %47) (%41 ((%4 %47)
       $0)))))))`)
  val rmDupes_twice =
    DT(["DISK_THM"], [], `(%7 (\%52. ((%3 (%41 (%41 $0))) (%41 $0))))`)
  val delete_lts =
    DT(["DISK_THM"], [],
       `(%1 (\%47. (%7 (\%52. ((%20 ((%22 $1) $0)) ((%149 (%138 $0)) ((%150
       $1) (%138 ((%4 $1) $0)))))))))`)
  val delete_lts_card =
    DT(["DISK_THM"], [],
       `(%1 (\%47. (%7 (\%52. ((%20 ((%22 $1) $0)) ((%97 (%151 (%138 $0)))
       (%151 (%138 ((%4 $1) $0)))))))))`)
  val rmDupes_lts =
    DT(["DISK_THM"], [], `(%7 (\%52. ((%149 (%138 $0)) (%138 (%41 $0)))))`)
  val rmDupes_lts_card =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%58 (%89 (%41 $0))) (%151 (%138 (%41 $0))))))`)
  val rmDupes_lts_card_eq =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%58 (%151 (%138 $0))) (%151 (%138 (%41 $0))))))`)
  val mem_subset_len =
    DT(["DISK_THM"], [],
       `(%7 (\%103. (%7 (\%104. ((%20 (%1 (\%50. ((%20 ((%22 $0) (%41 $2)))
       ((%22 $0) $1))))) ((%88 (%89 $0)) (%89 (%41 $1))))))))`)
  val list_set_len =
    DT(["DISK_THM"], [],
       `(%7 (\%103. (%129 (\%152. ((%20 ((%88 (%89 (%41 $1))) (%132 $0)))
       ((%88 (%151 (%138 $1))) (%153 (%154 $0))))))))`)
  val set_neq_len =
    DT(["DISK_THM"], [],
       `(%95 (\%155. ((%20 (%137 $0)) ((%20 (%21 ((%149 $0) %156))) ((%20
       ((%157 %156) $0)) ((%20 ((%88 (%151 $0)) (%151 %156))) ((%97 (%151
       $0)) (%151 %156))))))))`)
  val push_not_nil =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%52. (%21 ((%3 ((%53 $0) $1)) %5))))))`)
  val listNotEmpty =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 (%99 (\%50. ((%22 $0) $1)))) (%21 ((%3 $0)
       %5)))))`)
  val rev_nil =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%93 ((%3 (%158 $0)) %5)) ((%3 $0) %5))))`)
  val list_exists_mem =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 (%21 ((%3 $0) %5))) (%99 (\%50. ((%22 $0)
       $1))))))`)
  val FLAT_APPEND_DISTRIB =
    DT(["DISK_THM"], [],
       `(%159 (\%160. (%159 (\%161. ((%3 (%162 ((%163 $1) $0))) ((%102
       (%162 $1)) (%162 $0)))))))`)
  val flat_map_mem =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%129 (\%164. ((%20 ((%22 $1) (%162 ((%165 %166) $0))))
       (%100 (\%167. ((%0 ((%168 $0) ((%165 %166) $1))) ((%22 $2)
       $0)))))))))`)
  val popl =
    DT(["DISK_THM"], [],
       `(%7 (\%52. (%54 (\%84. ((%20 ((%3 %37) ((%56 $1) $0))) (%100
       (\%169. (%100 (\%170. ((%0 ((%3 $3) ((%102 $1) $0))) ((%3 $0)
       %37)))))))))))`)
  val listappnil =
    DT(["DISK_THM"], [],
       `(%7 (\%37. ((%20 ((%3 $0) ((%102 %169) $0))) ((%3 %169) %5))))`)
  val rev_sing =
    DT(["DISK_THM"], [],
       `(%7 (\%92. ((%93 ((%3 (%158 $0)) ((%9 %171) %5))) ((%3 $0) ((%9
       %171) %5)))))`)
  val take1 =
    DT(["DISK_THM"], [],
       `((%0 ((%3 ((%83 %59) %5)) %5)) ((%0 ((%3 ((%83 (%72 %71)) ((%9 %2)
       %70))) (((%10 ((%58 (%72 %71)) %59)) %5) ((%9 %2) ((%83 ((%60 (%72
       %71)) (%61 (%62 %63)))) %70))))) ((%3 ((%83 %59) ((%9 %2) %70)))
       (((%10 %74) %5) ((%9 %2) ((%83 ((%60 %59) (%61 (%62 %63))))
       %70))))))`)
  val take1_ind =
    DT(["DISK_THM"], [],
       `(%172 (\%173. ((%20 ((%0 (%54 (\%71. (($1 (%72 $0)) %5)))) ((%0
       (($0 %59) %5)) ((%0 (%54 (\%71. (%1 (\%2. (%7 (\%70. ((%20 ((%20
       (%21 ((%58 (%72 $2)) %59))) (($3 ((%60 (%72 $2)) (%61 (%62 %63))))
       $0))) (($3 (%72 $2)) ((%9 $1) $0)))))))))) (%1 (\%2. (%7 (\%70.
       ((%20 ((%20 (%21 %74)) (($2 ((%60 %59) (%61 (%62 %63)))) $0))) (($2
       %59) ((%9 $1) $0))))))))))) (%54 (\%78. (%7 (\%28. (($2 $1)
       $0))))))))`)
  val take_len =
    DT(["DISK_THM"], [],
       `(%54 (\%84. (%7 (\%52. ((%20 (%21 ((%85 ((%86 $1) $0)) %91))) ((%88
       (%89 $0)) $1))))))`)
  val take10 =
    DT(["DISK_THM"], [], `(%7 (\%52. ((%3 ((%83 %59) $0)) %5)))`)
  val take0 = DT(["DISK_THM"], [], `((%85 ((%86 %59) %52)) (%90 %5))`)
  val rev_len =
    DT(["DISK_THM"], [], `(%7 (\%52. ((%58 (%89 $0)) (%89 (%158 $0)))))`)
  val takeCoMap =
    DT(["DISK_THM"], [],
       `(%174 (\%175. (%176 (\%177. (%178 (\%179. ((%20 ((%180 ((%181 %84)
       ((%182 ((%183 $2) $1)) $0))) (%184 %185))) (%100 (\%186. ((%85 ((%86
       %84) ((%187 $2) $1))) (%90 $0)))))))))))`)
  val take1Map =
    DT(["DISK_THM"], [],
       `(%174 (\%175. (%7 (\%52. (%54 (\%84. ((%20 ((%88 (%89 $1)) $0))
       ((%188 ((%189 $0) ((%190 $2) $1))) ((%190 $2) ((%83 $0)
       $1))))))))))`)
  val revTakeMap =
    DT(["DISK_THM"], [],
       `(%54 (\%84. (%174 (\%175. (%7 (\%52. ((%20 ((%180 ((%181 $2) ((%190
       $1) $0))) (%184 %185))) ((%188 (%191 (%192 ((%181 $2) ((%190 $1)
       $0))))) (%191 ((%190 $1) (%193 ((%86 $2) $0))))))))))))`)
  val popnthm =
    DT(["DISK_THM"], [],
       `(%7 (\%169. (%7 (\%194. (%54 (\%84. ((%20 ((%58 (%89 $2)) $0)) ((%3
       ((%56 ((%102 $2) $1)) $0)) $1))))))))`)
  val take0out =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%85 ((%86 %59) $0)) (%90 %195))) ((%3 %195)
       %5))))`)
  val takenthm =
    DT(["DISK_THM"], [],
       `(%7 (\%169. (%7 (\%194. (%54 (\%84. ((%20 ((%58 (%89 $2)) $0))
       ((%20 (%21 ((%58 $0) %59))) ((%85 ((%86 $0) ((%102 $2) $1))) (%90
       $2))))))))))`)
  val pop0 = DT(["DISK_THM"], [], `(%7 (\%52. ((%3 ((%56 $0) %59)) $0)))`)
  val take_map =
    DT(["DISK_THM"], [],
       `(%196 (\%197. ((%20 ((%198 ((%199 (%200 %201)) $0)) (%202 %203)))
       ((%188 ((%204 %205) (%206 ((%199 (%200 %201)) $0)))) (%192 ((%181
       (%200 %201)) ((%204 %205) $0)))))))`)
  val take_valid =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%88 (%89 $0)) %84)) (%100 (\%37. ((%85 ((%86
       %84) $1)) (%90 $0)))))))`)
  val valid_take_map =
    DT(["DISK_THM"], [],
       `(%54 (\%84. (%7 (\%52. ((%20 ((%85 ((%86 $1) $0)) (%90 %37))) (%207
       (\%208. ((%180 ((%181 $2) ((%190 %175) $1))) (%184 $0)))))))))`)
  val map_rev =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%188 ((%190 %175) (%158 $0))) (%191 ((%190 %175)
       $0)))))`)
  val map_pop =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%188 ((%209 ((%190 %175) $0)) %84)) ((%190 %175) ((%56
       $0) %84)))))`)
  val take_pop =
    DT(["DISK_THM"], [],
       `(%7 (\%52. (%7 (\%210. (%54 (\%84. ((%20 ((%85 ((%86 $0) $2)) (%90
       $1))) ((%3 $2) ((%102 $1) ((%56 $2) $0))))))))))`)
  val take_mem =
    DT(["DISK_THM"], [],
       `(%54 (\%84. (%7 (\%52. ((%20 ((%85 ((%86 $1) $0)) (%90 %37))) (%1
       (\%50. ((%20 ((%22 $0) %37)) ((%22 $0) $1)))))))))`)
  val listeq =
    DT(["DISK_THM"], [],
       `(%7 (\%103. (%7 (\%104. (%1 (\%50. (%7 (\%211. (%7 (\%212. (%1
       (\%213. ((%20 ((%3 ((%102 ((%102 $5) ((%9 $3) %5))) $4)) ((%102
       ((%102 $2) ((%9 $0) %5))) $1))) ((%20 ((%0 (%21 (%214 $3))) ((%0
       (%21 (%214 $0))) ((%0 ((%215 %214) $4)) ((%215 %214) $1))))) ((%0
       ((%3 $5) $2)) ((%0 ((%11 $3) $0)) ((%3 $4) $1)))))))))))))))))`)
  val delete_prop =
    DT(["DISK_THM"], [],
       `(%95 (\%214. (%7 (\%52. ((%20 ((%215 $1) $0)) ((%215 $1) ((%4 %47)
       $0)))))))`)
  val rmDupes_prop =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 ((%215 %214) $0)) ((%215 %214) (%41 $0)))))`)
  val alld_delete =
    DT(["DISK_THM"], [],
       `(%7 (\%52. ((%20 (%216 $0)) (%1 (\%47. (%216 ((%4 $0) $1)))))))`)
  val alld_rmd =
    DT(["DISK_THM"], [],
       `(%7 (\%52. (%7 (\%210. ((%20 ((%3 (%41 $1)) $0)) (%216 $0))))))`)
  val diff_mem1 =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%103. (%7 (\%104. ((%20 ((%22 $2) ((%39 $1) $0)))
       ((%0 ((%22 $2) $1)) (%21 ((%22 $2) $0))))))))))`)
  val diff_mem2 =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%103. (%7 (\%104. ((%20 ((%22 $2) $1)) ((%20 (%21
       ((%22 $2) $0))) ((%22 $2) ((%39 $1) $0))))))))))`)
  val diff_mem =
    DT(["DISK_THM"], [],
       `(%1 (\%50. (%7 (\%103. (%7 (\%104. ((%93 ((%22 $2) ((%39 $1) $0)))
       ((%0 ((%22 $2) $1)) (%21 ((%22 $2) $0))))))))))`)
  val diff_DIFF =
    DT(["DISK_THM"], [],
       `(%7 (\%103. (%7 (\%104. ((%149 (%138 ((%39 $1) $0))) ((%217 (%138
       $1)) (%138 $0)))))))`)
  end
  val _ = DB.bindl "listLemmas"
  [("delete_def",delete_def,DB.Def),
   ("diff_tupled_primitive_def",diff_tupled_primitive_def,DB.Def),
   ("diff_curried_def",diff_curried_def,DB.Def),
   ("rmDupes_defn_primitive_def",rmDupes_defn_primitive_def,DB.Def),
   ("breakAtElem_def",breakAtElem_def,DB.Def),
   ("push_def",push_def,DB.Def), ("pop_def",pop_def,DB.Def),
   ("take1_defn_tupled_primitive_def",
    take1_defn_tupled_primitive_def,
    DB.Def), ("take1_defn_curried_def",take1_defn_curried_def,DB.Def),
   ("take_def",take_def,DB.Def), ("list_l1",list_l1,DB.Thm),
   ("filter_l1",filter_l1,DB.Thm), ("len_not_0",len_not_0,DB.Thm),
   ("filter_l2",filter_l2,DB.Thm), ("lres",lres,DB.Thm),
   ("lresb",lresb,DB.Thm), ("lreseq",lreseq,DB.Thm),
   ("rgr_r9",rgr_r9,DB.Thm), ("rgr_r9b",rgr_r9b,DB.Thm),
   ("rgr_r9eq",rgr_r9eq,DB.Thm), ("list_r1",list_r1,DB.Thm),
   ("list_r2",list_r2,DB.Thm), ("list_r6",list_r6,DB.Thm),
   ("list_lem1",list_lem1,DB.Thm), ("list_lem2",list_lem2,DB.Thm),
   ("list_lem3",list_lem3,DB.Thm), ("list_lem4",list_lem4,DB.Thm),
   ("l_lemma1",l_lemma1,DB.Thm), ("sl",sl,DB.Thm), ("sl_l2",sl_l2,DB.Thm),
   ("sl_l3",sl_l3,DB.Thm), ("len0",len0,DB.Thm),
   ("notLen1",notLen1,DB.Thm), ("listNotNull",listNotNull,DB.Thm),
   ("sl_l4",sl_l4,DB.Thm), ("sl_l5",sl_l5,DB.Thm),
   ("finiteLists",finiteLists,DB.Thm), ("diff_ind",diff_ind,DB.Thm),
   ("diff_def",diff_def,DB.Thm),
   ("delete_not_mem1",delete_not_mem1,DB.Thm),
   ("delete_append",delete_append,DB.Thm),
   ("not_mem_delete",not_mem_delete,DB.Thm),
   ("delete_not_mem2",delete_not_mem2,DB.Thm),
   ("delete_not_mem",delete_not_mem,DB.Thm),
   ("delete_mem_len",delete_mem_len,DB.Thm),
   ("delete_nil",delete_nil,DB.Thm),
   ("delete_mem_list",delete_mem_list,DB.Thm),
   ("delete_twice",delete_twice,DB.Thm),
   ("delete_diff_elem",delete_diff_elem,DB.Thm),
   ("rmDupes",rmDupes,DB.Thm), ("rmDupes_ind",rmDupes_ind,DB.Thm),
   ("rmd_r2_1",rmd_r2_1,DB.Thm), ("rmd_r2_2",rmd_r2_2,DB.Thm),
   ("rmd_r2",rmd_r2,DB.Thm), ("rmDupes_not_nil",rmDupes_not_nil,DB.Thm),
   ("rmd_mem_list1",rmd_mem_list1,DB.Thm),
   ("rmd_mem_list2",rmd_mem_list2,DB.Thm),
   ("rmd_mem_list",rmd_mem_list,DB.Thm),
   ("rmDupes_len",rmDupes_len,DB.Thm), ("rmd_del",rmd_del,DB.Thm),
   ("rmda_del_rmda",rmda_del_rmda,DB.Thm),
   ("rmDupes_twice",rmDupes_twice,DB.Thm),
   ("delete_lts",delete_lts,DB.Thm),
   ("delete_lts_card",delete_lts_card,DB.Thm),
   ("rmDupes_lts",rmDupes_lts,DB.Thm),
   ("rmDupes_lts_card",rmDupes_lts_card,DB.Thm),
   ("rmDupes_lts_card_eq",rmDupes_lts_card_eq,DB.Thm),
   ("mem_subset_len",mem_subset_len,DB.Thm),
   ("list_set_len",list_set_len,DB.Thm),
   ("set_neq_len",set_neq_len,DB.Thm),
   ("push_not_nil",push_not_nil,DB.Thm),
   ("listNotEmpty",listNotEmpty,DB.Thm), ("rev_nil",rev_nil,DB.Thm),
   ("list_exists_mem",list_exists_mem,DB.Thm),
   ("FLAT_APPEND_DISTRIB",FLAT_APPEND_DISTRIB,DB.Thm),
   ("flat_map_mem",flat_map_mem,DB.Thm), ("popl",popl,DB.Thm),
   ("listappnil",listappnil,DB.Thm), ("rev_sing",rev_sing,DB.Thm),
   ("take1",take1,DB.Thm), ("take1_ind",take1_ind,DB.Thm),
   ("take_len",take_len,DB.Thm), ("take10",take10,DB.Thm),
   ("take0",take0,DB.Thm), ("rev_len",rev_len,DB.Thm),
   ("takeCoMap",takeCoMap,DB.Thm), ("take1Map",take1Map,DB.Thm),
   ("revTakeMap",revTakeMap,DB.Thm), ("popnthm",popnthm,DB.Thm),
   ("take0out",take0out,DB.Thm), ("takenthm",takenthm,DB.Thm),
   ("pop0",pop0,DB.Thm), ("take_map",take_map,DB.Thm),
   ("take_valid",take_valid,DB.Thm),
   ("valid_take_map",valid_take_map,DB.Thm), ("map_rev",map_rev,DB.Thm),
   ("map_pop",map_pop,DB.Thm), ("take_pop",take_pop,DB.Thm),
   ("take_mem",take_mem,DB.Thm), ("listeq",listeq,DB.Thm),
   ("delete_prop",delete_prop,DB.Thm),
   ("rmDupes_prop",rmDupes_prop,DB.Thm),
   ("alld_delete",alld_delete,DB.Thm), ("alld_rmd",alld_rmd,DB.Thm),
   ("diff_mem1",diff_mem1,DB.Thm), ("diff_mem2",diff_mem2,DB.Thm),
   ("diff_mem",diff_mem,DB.Thm), ("diff_DIFF",diff_DIFF,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("containerLemmasTheory.containerLemmas_grammars",
                          containerLemmasTheory.containerLemmas_grammars),
                         ("stringTheory.string_grammars",
                          stringTheory.string_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "delete")
        {Name = "delete", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "diff_tupled")
        {Name = "diff_tupled", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "diff")
        {Name = "diff", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "rmDupes")
        {Name = "rmDupes", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "breakAtElem")
        {Name = "breakAtElem", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "push")
        {Name = "push", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "pop")
        {Name = "pop", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "take1_defn_tupled")
        {Name = "take1_defn_tupled", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "take1")
        {Name = "take1", Thy = "listLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "take")
        {Name = "take", Thy = "listLemmas"}
  val listLemmas_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [delete_def];  
  
  val _ = computeLib.add_funs [diff_def];  
  
  val _ = computeLib.add_funs [breakAtElem_def];  
  
  val _ = computeLib.add_funs [push_def];  
  
  val _ = computeLib.add_funs [pop_def];  
  
  val _ = computeLib.add_funs [take_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
