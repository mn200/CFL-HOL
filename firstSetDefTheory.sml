structure firstSetDefTheory :> firstSetDefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading firstSetDefTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open parserDefTheory
  in end;
  val _ = Theory.link_parents
          ("firstSetDef",
          Arbnum.fromString "1203551184",
          Arbnum.fromString "973331")
          [("parserDef",
           Arbnum.fromString "1203551171",
           Arbnum.fromString "311592")];
  val _ = Theory.incorporate_types "firstSetDef" [];
  val _ = Theory.incorporate_consts "firstSetDef"
     [("firstSet",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))))),
      ("firstSetML",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] -->
          T"list" "list" [T"symbol" "regexp" []])))),
      ("firstSet1_defn_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] -->
         T"list" "list" [T"symbol" "regexp" []]))),
      ("firstSet1",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"list" "list" [T"symbol" "regexp" []] -->
           T"list" "list" [T"symbol" "regexp" []]))))),
      ("firstSetList",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"symbol" "regexp" [] --> bool)))))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"g" (T"grammar" "grammarDef" []),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"l" (T"list" "list" [T"symbol" "regexp" []]),
   C"=" "min"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   C"firstSetList" "firstSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"symbol" "regexp" [] --> bool)))),
   C"GSPEC" "pred_set"
    (((T"string" "string" [] -->
       T"prod" "pair" [T"symbol" "regexp" [], bool]) -->
      (T"symbol" "regexp" [] --> bool))), V"fst" (T"string" "string" []),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (bool --> T"prod" "pair" [T"symbol" "regexp" [], bool]))),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"?" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"rst" (T"list" "list" [T"symbol" "regexp" []]),
   C"RTC" "relation"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)) -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"derives" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"APPEND" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"CONS" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"NIL" "list" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"sym" (T"symbol" "regexp" []),
   C"=" "min"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"firstSetML" "firstSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"symbol" "regexp" [] --> T"list" "list" [T"symbol" "regexp" []]))),
   C"firstSet1" "firstSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   V"x" (T"grammar" "grammarDef" []),
   V"x1" (T"list" "list" [T"symbol" "regexp" []]),
   V"x2" (T"list" "list" [T"symbol" "regexp" []]),
   C"firstSet1_defn_tupled" "firstSetDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] -->
      T"list" "list" [T"symbol" "regexp" []])),
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
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       T"list" "list" [T"symbol" "regexp" []]) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] -->
        T"list" "list" [T"symbol" "regexp" []]) --> bool))),
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
             T"list" "list" [T"symbol" "regexp" []]]] -->
         T"list" "list" [T"symbol" "regexp" []]) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"list" "list" [T"symbol" "regexp" []]]] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"list" "list" [T"symbol" "regexp" []]]] -->
        T"list" "list" [T"symbol" "regexp" []])))),
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
   C"/\\" "bool" ((bool --> (bool --> bool))),
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
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"nt" (T"string" "string" []),
   C"!" "bool"
    (((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool)
      --> bool)),
   V"r" (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]),
   V"a" (T"list" "list" [T"symbol" "regexp" []]),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)),
   C"MEM" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"=" "min"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   C"getRhs" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"rules" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   C"NIL" "list" (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]),
   C"MEM" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   V"v15" (T"list" "list" [T"symbol" "regexp" []]),
   V"v14" (T"symbol" "regexp" []), V"v7" (T"string" "string" []),
   C"isTmnlSym" "regexp" ((T"symbol" "regexp" [] --> bool)),
   C"nullableML" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   V"v11" (T"list" "list" [T"symbol" "regexp" []]),
   V"v10" (T"symbol" "regexp" []), V"v6" (T"string" "string" []),
   V"firstSet1_defn_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   V"a'"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"list" "list" [T"symbol" "regexp" []]] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"list" "list" [T"symbol" "regexp" []]]] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"list" "list" [T"symbol" "regexp" []]]),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   V"v3" (T"list" "list" [T"symbol" "regexp" []]),
   C"list_case" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         T"list" "list" [T"symbol" "regexp" []])) -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"I" "combin"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   V"v4" (T"symbol" "regexp" []),
   V"v5" (T"list" "list" [T"symbol" "regexp" []]),
   C"symbol_case" "regexp"
    (((T"string" "string" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      ((T"string" "string" [] --> T"list" "list" [T"symbol" "regexp" []])
       -->
       (T"symbol" "regexp" [] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   V"ts" (T"string" "string" []), V"v12" (T"symbol" "regexp" []),
   V"v13" (T"list" "list" [T"symbol" "regexp" []]),
   C"COND" "bool"
    ((bool -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"LET" "bool"
    (((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"symbol" "regexp" []]) -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"symbol" "regexp" []]))),
   C"rmDupes" "listLemmas"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"FLAT" "list"
    ((T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
      T"list" "list" [T"symbol" "regexp" []])),
   C"MAP" "list"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       T"list" "list" [T"symbol" "regexp" []]) -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   V"v16" (T"symbol" "regexp" []),
   V"v17" (T"list" "list" [T"symbol" "regexp" []]),
   C"firstSet" "firstSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool)))),
   V"s" (T"symbol" "regexp" []),
   C"IN" "bool"
    ((T"symbol" "regexp" [] -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   V"sfx" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"x" (T"list" "list" [alpha]), V"y" (T"list" "list" [alpha]),
   V"z" (T"list" "list" [alpha]),
   C"=" "min"
    ((T"list" "list" [alpha] --> (T"list" "list" [alpha] --> bool))),
   C"rmDupes" "listLemmas"
    ((T"list" "list" [alpha] --> T"list" "list" [alpha])),
   C"APPEND" "list"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"diff" "listLemmas"
    ((T"list" "list" [alpha] -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"=" "min" ((bool --> (bool --> bool))),
   V"r" (T"list" "list" [T"symbol" "regexp" []]),
   C"MEM" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         (T"list" "list" [T"symbol" "regexp" []] --> bool))) --> bool) -->
      bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   V"v" (T"grammar" "grammarDef" []),
   V"v1" (T"list" "list" [T"symbol" "regexp" []]),
   V"v2" (T"list" "list" [T"symbol" "regexp" []])]
  val DT = Thm.disk_thm share_table
  in
  val firstSetList_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. ((%4 ((%5 $1) $0)) (%6 (\%7. ((%8 (%9 $0)) (%10
       (\%11. (((%12 (%13 $3)) $2) ((%14 ((%15 (%9 $1)) %16))
       $0))))))))))))`)
  val firstSetML_def =
    DT([], [],
       `(%0 (\%1. (%17 (\%18. ((%19 ((%20 $1) $0)) (((%21 $1) %16) ((%15
       $0) %16)))))))`)
  val firstSet1_defn_curried_def =
    DT([], [],
       `(%0 (\%22. (%2 (\%23. (%2 (\%24. ((%19 (((%21 $2) $1) $0)) (%25
       ((%26 $2) ((%27 $1) $0))))))))))`)
  val firstSet1_defn_tupled_primitive_def =
    DT([], [],
       `((%28 %25) ((%29 (%30 (\%31. ((%32 (%33 $0)) ((%32 (%0 (\%1. (%2
       (\%34. (%35 (\%36. (%37 (\%38. (%2 (\%39. ((%40 ((%32 (%41 ((%42
       (%43 $2)) $3))) ((%32 ((%44 $1) ((%45 $2) (%46 $4)))) ((%32 (%41
       ((%44 $1) %47))) ((%48 $0) $1))))) (($5 ((%26 $4) ((%27 ((%15 (%43
       $2)) $3)) $0))) ((%26 $4) ((%27 $3) ((%15 (%43 $2))
       %16)))))))))))))))) ((%32 (%2 (\%49. (%17 (\%50. (%2 (\%34. (%0
       (\%1. (%35 (\%51. ((%40 ((%32 (%41 (%52 (%43 $0)))) (((%53 $1) %16)
       ((%15 (%43 $0)) %16)))) (($5 ((%26 $1) ((%27 $2) ((%15 (%43 $0))
       %16)))) ((%26 $1) ((%27 $2) ((%15 (%43 $0)) ((%15 $3)
       $4))))))))))))))))) ((%32 (%2 (\%49. (%17 (\%50. (%2 (\%34. (%0
       (\%1. (%35 (\%51. ((%40 ((%32 (%41 (%52 (%43 $0)))) (((%53 $1) %16)
       ((%15 (%43 $0)) %16)))) (($5 ((%26 $1) ((%27 $2) ((%15 $3) $4))))
       ((%26 $1) ((%27 $2) ((%15 (%43 $0)) ((%15 $3) $4)))))))))))))))))
       ((%32 (%2 (\%49. (%17 (\%50. (%2 (\%34. (%0 (\%1. (%35 (\%51. ((%40
       ((%32 (%41 (%52 (%43 $0)))) (%41 (((%53 $1) %16) ((%15 (%43 $0))
       %16))))) (($5 ((%26 $1) ((%27 $2) ((%15 (%43 $0)) %16)))) ((%26 $1)
       ((%27 $2) ((%15 (%43 $0)) ((%15 $3) $4))))))))))))))))) ((%32 (%2
       (\%54. (%17 (\%55. (%2 (\%34. (%0 (\%1. (%35 (\%56. ((%40 ((%32 (%41
       (%52 (%9 $0)))) (%41 (((%53 $1) %16) ((%15 (%9 $0)) %16))))) (($5
       ((%26 $1) ((%27 $2) ((%15 (%9 $0)) %16)))) ((%26 $1) ((%27 $2) ((%15
       (%9 $0)) ((%15 $3) $4))))))))))))))))) ((%32 (%2 (\%54. (%17 (\%55.
       (%2 (\%34. (%0 (\%1. (%35 (\%56. ((%40 ((%32 (%41 (%52 (%9 $0))))
       (((%53 $1) %16) ((%15 (%9 $0)) %16)))) (($5 ((%26 $1) ((%27 $2)
       ((%15 $3) $4)))) ((%26 $1) ((%27 $2) ((%15 (%9 $0)) ((%15 $3)
       $4))))))))))))))))) (%2 (\%54. (%17 (\%55. (%2 (\%34. (%0 (\%1. (%35
       (\%56. ((%40 ((%32 (%41 (%52 (%9 $0)))) (((%53 $1) %16) ((%15 (%9
       $0)) %16)))) (($5 ((%26 $1) ((%27 $2) ((%15 (%9 $0)) %16)))) ((%26
       $1) ((%27 $2) ((%15 (%9 $0)) ((%15 $3) $4))))))))))))))))))))))))))
       (\%57. (\%58. ((%59 (\%1. (\%60. ((%61 (\%34. (\%62. (((%63 (%64
       %16)) (\%65. (\%66. (((%67 (\%68. (((%63 (%64 ((%15 (%9 $0)) %16)))
       (\%69. (\%70. (%64 (((%71 (%52 (%9 $2))) ((%15 (%9 $2)) %16)) (((%71
       (((%53 $8) %16) ((%15 (%9 $2)) %16))) ((%14 ($10 ((%26 $8) ((%27 $6)
       ((%15 (%9 $2)) %16))))) ($10 ((%26 $8) ((%27 $6) ((%15 $1) $0))))))
       ($10 ((%26 $8) ((%27 $6) ((%15 (%9 $2)) %16)))))))))) $1))) (\%36.
       (((%63 (%64 (((%71 ((%42 (%43 $0)) $4)) %16) ((%72 (\%38. (((%71
       ((%44 $0) %47)) %16) (%73 (%74 ((%75 (\%39. ($10 ((%26 $8) ((%27
       ((%15 (%43 $2)) $6)) $0))))) $0)))))) ((%45 $0) (%46 $6)))))) (\%76.
       (\%77. (%64 (((%71 (%52 (%43 $2))) ((%15 (%43 $2)) %16)) (((%71
       (((%53 $8) %16) ((%15 (%43 $2)) %16))) ((%14 ($10 ((%26 $8) ((%27
       $6) ((%15 (%43 $2)) %16))))) ($10 ((%26 $8) ((%27 $6) ((%15 $1)
       $0)))))) ($10 ((%26 $8) ((%27 $6) ((%15 (%43 $2)) %16))))))))))
       $1))) $1)))) $0)))) $0)))) $0)))))`)
  val firstSet_def =
    DT([], [],
       `(%0 (\%1. (%17 (\%18. ((%4 ((%78 $1) $0)) (%6 (\%7. ((%8 (%9 $0))
       (%10 (\%11. (((%12 (%13 $3)) ((%15 $2) %16)) ((%14 ((%15 (%9 $1))
       %16)) $0))))))))))))`)
  val firstSet1 =
    DT(["DISK_THM"], [],
       `((%32 ((%19 (((%21 %1) %34) %16)) %16)) ((%32 ((%19 (((%21 %1) %34)
       ((%15 (%9 %68)) %16))) ((%15 (%9 %68)) %16))) ((%32 ((%19 (((%21 %1)
       %34) ((%15 (%43 %36)) %16))) (((%71 ((%42 (%43 %36)) %34)) %16)
       ((%72 (\%38. (((%71 ((%44 $0) %47)) %16) (%73 (%74 ((%75 (\%39.
       (((%21 %1) ((%15 (%43 %36)) %34)) $0))) $0)))))) ((%45 %36) (%46
       %1)))))) ((%32 ((%19 (((%21 %1) %34) ((%15 (%43 %51)) ((%15 %50)
       %49)))) (((%71 (%52 (%43 %51))) ((%15 (%43 %51)) %16)) (((%71 (((%53
       %1) %16) ((%15 (%43 %51)) %16))) ((%14 (((%21 %1) %34) ((%15 (%43
       %51)) %16))) (((%21 %1) %34) ((%15 %50) %49)))) (((%21 %1) %34)
       ((%15 (%43 %51)) %16)))))) ((%19 (((%21 %1) %34) ((%15 (%9 %56))
       ((%15 %55) %54)))) (((%71 (%52 (%9 %56))) ((%15 (%9 %56)) %16))
       (((%71 (((%53 %1) %16) ((%15 (%9 %56)) %16))) ((%14 (((%21 %1) %34)
       ((%15 (%9 %56)) %16))) (((%21 %1) %34) ((%15 %55) %54)))) (((%21 %1)
       %34) ((%15 (%9 %56)) %16)))))))))`)
  val firstSet1Eq1 =
    DT(["DISK_THM", "MK_THM"], [],
       `(%0 (\%1. (%2 (\%34. (%2 (\%3. ((%40 ((%42 %79) (((%21 $2) $1)
       $0))) ((%80 %79) ((%5 $2) $0)))))))))`)
  val derivesFirstSet =
    DT(["DISK_THM"], [],
       `((%40 (((%13 %1) ((%15 (%43 %36)) %16)) ((%15 (%9 %68)) %81)))
       ((%42 (%9 %68)) (((%21 %1) %16) ((%15 (%43 %36)) %16))))`)
  val rmd_r1 =
    DT(["DISK_THM", "MK_THM"], [],
       `(%82 (\%83. (%82 (\%84. (%82 (\%85. ((%86 (%87 ((%88 ((%88 $2) $1))
       $0))) ((%88 ((%88 (%87 $2)) (%87 ((%89 $1) $2)))) (%87 ((%89 $0)
       ((%88 $2) $1)))))))))))`)
  val getRhsNilRtc =
    DT(["DISK_THM"], [],
       `((%40 ((%44 ((%45 %36) (%46 %1))) %47)) (%2 (\%3. ((%40 (((%12 (%13
       %1)) ((%15 (%43 %36)) %16)) $0)) ((%19 $0) ((%15 (%43 %36))
       %16))))))`)
  val getRhsNilMem =
    DT(["DISK_THM"], [],
       `((%90 ((%44 ((%45 %36) (%46 %1))) %47)) (%41 (%10 (\%91. ((%92
       ((%93 %36) $0)) (%46 %1))))))`)
  val firstSet1_ind =
    DT(["DISK_THM"], [],
       `(%94 (\%95. ((%40 ((%32 (%0 (\%1. (%2 (\%34. ((($2 $1) $0)
       %16)))))) ((%32 (%0 (\%1. (%2 (\%34. (%35 (\%68. ((($3 $2) $1) ((%15
       (%9 $0)) %16))))))))) ((%32 (%0 (\%1. (%2 (\%34. (%35 (\%36. ((%40
       (%37 (\%38. (%2 (\%39. ((%40 ((%32 (%41 ((%42 (%43 $2)) $3))) ((%32
       ((%44 $1) ((%45 $2) (%46 $4)))) ((%32 (%41 ((%44 $1) %47))) ((%48
       $0) $1))))) ((($5 $4) ((%15 (%43 $2)) $3)) $0))))))) ((($3 $2) $1)
       ((%15 (%43 $0)) %16)))))))))) ((%32 (%0 (\%1. (%2 (\%34. (%35 (\%51.
       (%17 (\%50. (%2 (\%49. ((%40 ((%32 ((%40 ((%32 (%41 (%52 (%43 $2))))
       (%41 (((%53 $4) %16) ((%15 (%43 $2)) %16))))) ((($5 $4) $3) ((%15
       (%43 $2)) %16)))) ((%32 ((%40 ((%32 (%41 (%52 (%43 $2)))) (((%53 $4)
       %16) ((%15 (%43 $2)) %16)))) ((($5 $4) $3) ((%15 $1) $0)))) ((%40
       ((%32 (%41 (%52 (%43 $2)))) (((%53 $4) %16) ((%15 (%43 $2)) %16))))
       ((($5 $4) $3) ((%15 (%43 $2)) %16)))))) ((($5 $4) $3) ((%15 (%43
       $2)) ((%15 $1) $0))))))))))))))) (%0 (\%1. (%2 (\%34. (%35 (\%56.
       (%17 (\%55. (%2 (\%54. ((%40 ((%32 ((%40 ((%32 (%41 (%52 (%9 $2))))
       (%41 (((%53 $4) %16) ((%15 (%9 $2)) %16))))) ((($5 $4) $3) ((%15 (%9
       $2)) %16)))) ((%32 ((%40 ((%32 (%41 (%52 (%9 $2)))) (((%53 $4) %16)
       ((%15 (%9 $2)) %16)))) ((($5 $4) $3) ((%15 $1) $0)))) ((%40 ((%32
       (%41 (%52 (%9 $2)))) (((%53 $4) %16) ((%15 (%9 $2)) %16)))) ((($5
       $4) $3) ((%15 (%9 $2)) %16)))))) ((($5 $4) $3) ((%15 (%9 $2)) ((%15
       $1) $0))))))))))))))))))) (%0 (\%96. (%2 (\%97. (%2 (\%98. ((($3 $2)
       $1) $0))))))))))`)
  end
  val _ = DB.bindl "firstSetDef"
  [("firstSetList_def",firstSetList_def,DB.Def),
   ("firstSetML_def",firstSetML_def,DB.Def),
   ("firstSet1_defn_curried_def",firstSet1_defn_curried_def,DB.Def),
   ("firstSet1_defn_tupled_primitive_def",
    firstSet1_defn_tupled_primitive_def,
    DB.Def), ("firstSet_def",firstSet_def,DB.Def),
   ("firstSet1",firstSet1,DB.Thm), ("firstSet1Eq1",firstSet1Eq1,DB.Thm),
   ("derivesFirstSet",derivesFirstSet,DB.Thm), ("rmd_r1",rmd_r1,DB.Thm),
   ("getRhsNilRtc",getRhsNilRtc,DB.Thm),
   ("getRhsNilMem",getRhsNilMem,DB.Thm),
   ("firstSet1_ind",firstSet1_ind,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("parserDefTheory.parserDef_grammars",
                          parserDefTheory.parserDef_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "firstSet")
        {Name = "firstSet", Thy = "firstSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "firstSet1_defn_tupled")
        {Name = "firstSet1_defn_tupled", Thy = "firstSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "firstSet1")
        {Name = "firstSet1", Thy = "firstSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "firstSetML")
        {Name = "firstSetML", Thy = "firstSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "firstSetList")
        {Name = "firstSetList", Thy = "firstSetDef"}
  val firstSetDef_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [firstSet_def];  
  
  val _ = computeLib.add_funs [firstSetML_def];  
  
  val _ = computeLib.add_funs [firstSetList_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
