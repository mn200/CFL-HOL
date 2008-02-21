structure followSetDefTheory :> followSetDefTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading followSetDefTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open firstSetDefTheory
  in end;
  val _ = Theory.link_parents
          ("followSetDef",
          Arbnum.fromString "1203551207",
          Arbnum.fromString "541097")
          [("firstSetDef",
           Arbnum.fromString "1203551184",
           Arbnum.fromString "973331")];
  val _ = Theory.incorporate_types "followSetDef" [];
  val _ = Theory.incorporate_consts "followSetDef"
     [("followSetML",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))))),
      ("followRuleML_defn_tupled",
       ((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
         (T"symbol" "regexp" [] --> bool)))),
      ("followSet",
       ((T"grammar" "grammarDef" [] -->
         (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))))),
      ("followRuleML",
       ((T"grammar" "grammarDef" [] -->
         (T"list" "list" [T"symbol" "regexp" []] -->
          (T"symbol" "regexp" [] -->
           (T"rule" "grammarDef" [] -->
            (T"symbol" "regexp" [] --> bool)))))))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" (((T"grammar" "grammarDef" [] --> bool) --> bool)),
   V"g" (T"grammar" "grammarDef" []),
   C"!" "bool" (((T"symbol" "regexp" [] --> bool) --> bool)),
   V"sym" (T"symbol" "regexp" []),
   C"=" "min"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   C"followSet" "followSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool)))),
   C"GSPEC" "pred_set"
    (((T"string" "string" [] -->
       T"prod" "pair" [T"symbol" "regexp" [], bool]) -->
      (T"symbol" "regexp" [] --> bool))), V"ts" (T"string" "string" []),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (bool --> T"prod" "pair" [T"symbol" "regexp" [], bool]))),
   C"TS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"?" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"s" (T"list" "list" [T"symbol" "regexp" []]),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"MEM" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"list" "list" [T"list" "list" [T"symbol" "regexp" []]] --> bool))),
   C"MAP" "list"
    (((T"rule" "grammarDef" [] --> T"list" "list" [T"symbol" "regexp" []])
      -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [T"list" "list" [T"symbol" "regexp" []]]))),
   C"ruleRhs" "grammarDef"
    ((T"rule" "grammarDef" [] --> T"list" "list" [T"symbol" "regexp" []])),
   C"rules" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      T"list" "list" [T"rule" "grammarDef" []])),
   V"pfx" (T"list" "list" [T"symbol" "regexp" []]),
   V"sfx" (T"list" "list" [T"symbol" "regexp" []]),
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
   C"=" "min"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
       (T"symbol" "regexp" [] --> bool)) -->
      ((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
        (T"symbol" "regexp" [] --> bool)) --> bool))),
   C"followRuleML_defn_tupled" "followSetDef"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]]
      --> (T"symbol" "regexp" [] --> bool))),
   C"WFREC" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] --> bool))
      -->
      (((T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
         (T"symbol" "regexp" [] --> bool)) -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
         (T"symbol" "regexp" [] --> bool))) -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
        (T"symbol" "regexp" [] --> bool))))),
   C"@" "min"
    ((((T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
        (T"prod" "pair"
          [T"grammar" "grammarDef" [],
           T"prod" "pair"
            [T"list" "list" [T"symbol" "regexp" []],
             T"prod" "pair"
              [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] --> bool))
       --> bool) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
        bool)))),
   V"R"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]]
      -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] --> bool))),
   C"WF" "relation"
    (((T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
       (T"prod" "pair"
         [T"grammar" "grammarDef" [],
          T"prod" "pair"
           [T"list" "list" [T"symbol" "regexp" []],
            T"prod" "pair"
             [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] --> bool))
      --> bool)),
   C"!" "bool"
    (((T"list" "list" [T"symbol" "regexp" []] --> bool) --> bool)),
   V"t" (T"list" "list" [T"symbol" "regexp" []]),
   V"h" (T"symbol" "regexp" []),
   C"!" "bool" (((T"string" "string" [] --> bool) --> bool)),
   V"l" (T"string" "string" []),
   V"sn" (T"list" "list" [T"symbol" "regexp" []]),
   C"!" "bool" (((T"rule" "grammarDef" [] --> bool) --> bool)),
   V"a" (T"rule" "grammarDef" []),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)),
   C"MEM" "list"
    ((T"symbol" "regexp" [] -->
      (T"list" "list" [T"symbol" "regexp" []] --> bool))),
   C"IN" "bool"
    ((T"symbol" "regexp" [] -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   C"allSyms" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"NTS" "regexp" ((T"string" "string" [] --> T"symbol" "regexp" [])),
   C"nonTerminalsML" "grammarDef"
    ((T"grammar" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))),
   C"=" "min"
    ((T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool))),
   C"nullableML" "grammarDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] --> bool)))),
   C"MEM" "list"
    ((T"rule" "grammarDef" [] -->
      (T"list" "list" [T"rule" "grammarDef" []] --> bool))),
   C"," "pair"
    ((T"grammar" "grammarDef" [] -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]
       -->
       T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]]))),
   C"," "pair"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []] -->
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"symbol" "regexp" [], T"rule" "grammarDef" []]]))),
   C"," "pair"
    ((T"symbol" "regexp" [] -->
      (T"rule" "grammarDef" [] -->
       T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]))),
   C"rule" "grammarDef"
    ((T"string" "string" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       T"rule" "grammarDef" []))),
   V"followRuleML_defn_tupled"
    ((T"prod" "pair"
       [T"grammar" "grammarDef" [],
        T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]]
      --> (T"symbol" "regexp" [] --> bool))),
   V"a'"
    (T"prod" "pair"
      [T"grammar" "grammarDef" [],
       T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair"
          [T"symbol" "regexp" [], T"rule" "grammarDef" []]]]),
   C"pair_case" "pair"
    (((T"grammar" "grammarDef" [] -->
       (T"prod" "pair"
         [T"list" "list" [T"symbol" "regexp" []],
          T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]
        --> (T"symbol" "regexp" [] --> bool))) -->
      (T"prod" "pair"
        [T"grammar" "grammarDef" [],
         T"prod" "pair"
          [T"list" "list" [T"symbol" "regexp" []],
           T"prod" "pair"
            [T"symbol" "regexp" [], T"rule" "grammarDef" []]]] -->
       (T"symbol" "regexp" [] --> bool)))),
   V"v1"
    (T"prod" "pair"
      [T"list" "list" [T"symbol" "regexp" []],
       T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]),
   C"pair_case" "pair"
    (((T"list" "list" [T"symbol" "regexp" []] -->
       (T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []] -->
        (T"symbol" "regexp" [] --> bool))) -->
      (T"prod" "pair"
        [T"list" "list" [T"symbol" "regexp" []],
         T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]]
       --> (T"symbol" "regexp" [] --> bool)))),
   V"v3" (T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []]),
   C"pair_case" "pair"
    (((T"symbol" "regexp" [] -->
       (T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool))) -->
      (T"prod" "pair" [T"symbol" "regexp" [], T"rule" "grammarDef" []] -->
       (T"symbol" "regexp" [] --> bool)))),
   V"v5" (T"rule" "grammarDef" []),
   C"rule_case" "grammarDef"
    (((T"string" "string" [] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        (T"symbol" "regexp" [] --> bool))) -->
      (T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))),
   V"v7" (T"list" "list" [T"symbol" "regexp" []]),
   C"list_case" "list"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         (T"symbol" "regexp" [] --> bool))) -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        (T"symbol" "regexp" [] --> bool))))),
   C"I" "combin"
    (((T"symbol" "regexp" [] --> bool) -->
      (T"symbol" "regexp" [] --> bool))),
   C"EMPTY" "pred_set" ((T"symbol" "regexp" [] --> bool)),
   C"COND" "bool"
    ((bool -->
      ((T"symbol" "regexp" [] --> bool) -->
       ((T"symbol" "regexp" [] --> bool) -->
        (T"symbol" "regexp" [] --> bool))))),
   C"UNION" "pred_set"
    (((T"symbol" "regexp" [] --> bool) -->
      ((T"symbol" "regexp" [] --> bool) -->
       (T"symbol" "regexp" [] --> bool)))),
   C"LIST_TO_SET" "list"
    ((T"list" "list" [T"symbol" "regexp" []] -->
      (T"symbol" "regexp" [] --> bool))),
   C"firstSet1" "firstSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"list" "list" [T"symbol" "regexp" []] -->
        T"list" "list" [T"symbol" "regexp" []])))),
   C"BIGUNION" "pred_set"
    ((((T"symbol" "regexp" [] --> bool) --> bool) -->
      (T"symbol" "regexp" [] --> bool))),
   C"LIST_TO_SET" "list"
    ((T"list" "list" [(T"symbol" "regexp" [] --> bool)] -->
      ((T"symbol" "regexp" [] --> bool) --> bool))),
   C"MAP" "list"
    (((T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)) -->
      (T"list" "list" [T"rule" "grammarDef" []] -->
       T"list" "list" [(T"symbol" "regexp" [] --> bool)]))),
   V"x" (T"grammar" "grammarDef" []),
   V"x1" (T"list" "list" [T"symbol" "regexp" []]),
   V"x2" (T"symbol" "regexp" []), V"x3" (T"rule" "grammarDef" []),
   C"followRuleML" "followSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"symbol" "regexp" [] -->
        (T"rule" "grammarDef" [] --> (T"symbol" "regexp" [] --> bool)))))),
   C"followSetML" "followSetDef"
    ((T"grammar" "grammarDef" [] -->
      (T"symbol" "regexp" [] --> (T"symbol" "regexp" [] --> bool)))),
   C"!" "bool"
    ((((T"grammar" "grammarDef" [] -->
        (T"list" "list" [T"symbol" "regexp" []] -->
         (T"symbol" "regexp" [] --> (T"rule" "grammarDef" [] --> bool))))
       --> bool) --> bool)),
   V"P"
    ((T"grammar" "grammarDef" [] -->
      (T"list" "list" [T"symbol" "regexp" []] -->
       (T"symbol" "regexp" [] --> (T"rule" "grammarDef" [] --> bool))))),
   V"v" (T"grammar" "grammarDef" []),
   V"v1" (T"list" "list" [T"symbol" "regexp" []]),
   V"v2" (T"symbol" "regexp" []), V"v3" (T"rule" "grammarDef" []),
   V"r" (T"rule" "grammarDef" []), V"s" (T"symbol" "regexp" [])]
  val DT = Thm.disk_thm share_table
  in
  val followSet_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. ((%4 ((%5 $1) $0)) (%6 (\%7. ((%8 (%9 $0)) (%10
       (\%11. ((%12 ((%13 $0) ((%14 %15) (%16 $3)))) (%10 (\%17. (%10
       (\%18. (((%19 (%20 $5)) $2) ((%21 ((%21 ((%21 $1) ((%22 $4) %23)))
       ((%22 (%9 $3)) %23))) $0)))))))))))))))))`)
  val followRuleML_defn_tupled_primitive_def =
    DT([], [],
       `((%24 %25) ((%26 (%27 (\%28. ((%12 (%29 $0)) ((%12 (%30 (\%31. (%2
       (\%32. (%33 (\%34. (%0 (\%1. (%30 (\%35. (%2 (\%3. (%36 (\%37. ((%38
       ((%12 ((%12 (%39 ((%40 $1) $2))) ((%41 $1) (%42 $3)))) ((%12 ((%41
       (%43 $4)) (%44 $3))) ((%12 ((%45 $5) $1)) ((%12 (((%46 $3) %23) $6))
       ((%47 $0) (%16 $3))))))) (($7 ((%48 $3) ((%49 ((%22 $1) $2)) ((%50
       (%43 $4)) $0)))) ((%48 $3) ((%49 $2) ((%50 $1) ((%51 $4) ((%22 $5)
       $6)))))))))))))))))))))) ((%12 (%30 (\%31. (%2 (\%32. (%33 (\%34.
       (%0 (\%1. (%30 (\%35. (%2 (\%3. ((%38 ((%12 ((%12 (%39 ((%40 $0)
       $1))) ((%41 $0) (%42 $2)))) ((%12 ((%41 (%43 $3)) (%44 $2))) (%39
       ((%45 $4) $0))))) (($6 ((%48 $2) ((%49 $1) ((%50 $0) ((%51 $3)
       $5))))) ((%48 $2) ((%49 $1) ((%50 $0) ((%51 $3) ((%22 $4)
       $5)))))))))))))))))))) (%30 (\%31. (%2 (\%32. (%33 (\%34. (%0 (\%1.
       (%30 (\%35. (%2 (\%3. ((%38 ((%12 ((%12 (%39 ((%40 $0) $1))) ((%41
       $0) (%42 $2)))) ((%12 ((%41 (%43 $3)) (%44 $2))) ((%45 $4) $0))))
       (($6 ((%48 $2) ((%49 $1) ((%50 $0) ((%51 $3) $5))))) ((%48 $2) ((%49
       $1) ((%50 $0) ((%51 $3) ((%22 $4) $5))))))))))))))))))))))))) (\%52.
       (\%53. ((%54 (\%1. (\%55. ((%56 (\%35. (\%57. ((%58 (\%3. (\%59.
       ((%60 (\%34. (\%61. (((%62 (%63 %64)) (\%32. (\%31. (%63 (((%65
       ((%12 (%39 ((%40 $5) $7))) ((%41 $5) (%42 $9)))) (((%65 ((%41 (%43
       $3)) (%44 $9))) (((%65 ((%45 $1) $5)) ((%66 ((%66 (%67 (((%68 $9)
       %23) $0))) ($11 ((%48 $9) ((%49 $7) ((%50 $5) ((%51 $3) $0)))))))
       (((%65 (((%46 $9) %23) $0)) (%69 (%70 ((%71 (\%37. ($12 ((%48 $10)
       ((%49 ((%22 $6) $8)) ((%50 (%43 $4)) $0)))))) (%16 $9))))) %64)))
       ($11 ((%48 $9) ((%49 $7) ((%50 $5) ((%51 $3) $0))))))) %64))
       %64))))) $0)))) $0)))) $0)))) $0)))) $0)))))`)
  val followRuleML_defn_curried_def =
    DT([], [],
       `(%0 (\%72. (%30 (\%73. (%2 (\%74. (%36 (\%75. ((%4 ((((%76 $3) $2)
       $1) $0)) (%25 ((%48 $3) ((%49 $2) ((%50 $1) $0)))))))))))))`)
  val followSetML_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. ((%4 ((%77 $1) $0)) (%69 (%70 ((%71 (((%76 $1)
       %23) $0)) (%16 $1)))))))))`)
  val followRuleML =
    DT(["DISK_THM"], [],
       `((%12 ((%4 ((((%76 %1) %35) %3) ((%51 %34) %23))) %64)) ((%4
       ((((%76 %1) %35) %3) ((%51 %34) ((%22 %32) %31)))) (((%65 ((%12 (%39
       ((%40 %3) %35))) ((%41 %3) (%42 %1)))) (((%65 ((%41 (%43 %34)) (%44
       %1))) (((%65 ((%45 %32) %3)) ((%66 ((%66 (%67 (((%68 %1) %23) %31)))
       ((((%76 %1) %35) %3) ((%51 %34) %31)))) (((%65 (((%46 %1) %23) %31))
       (%69 (%70 ((%71 (\%37. ((((%76 %1) ((%22 %3) %35)) (%43 %34)) $0)))
       (%16 %1))))) %64))) ((((%76 %1) %35) %3) ((%51 %34) %31)))) %64))
       %64)))`)
  val followRuleML_ind =
    DT(["DISK_THM"], [],
       `(%78 (\%79. ((%38 ((%12 (%0 (\%1. (%30 (\%35. (%2 (\%3. (%33 (\%34.
       (((($4 $3) $2) $1) ((%51 $0) %23))))))))))) (%0 (\%1. (%30 (\%35.
       (%2 (\%3. (%33 (\%34. (%2 (\%32. (%30 (\%31. ((%38 ((%12 (%36 (\%37.
       ((%38 ((%12 ((%12 (%39 ((%40 $4) $5))) ((%41 $4) (%42 $6)))) ((%12
       ((%41 (%43 $3)) (%44 $6))) ((%12 ((%45 $2) $4)) ((%12 (((%46 $6)
       %23) $1)) ((%47 $0) (%16 $6))))))) (((($7 $6) ((%22 $4) $5)) (%43
       $3)) $0))))) ((%12 ((%38 ((%12 ((%12 (%39 ((%40 $3) $4))) ((%41 $3)
       (%42 $5)))) ((%12 ((%41 (%43 $2)) (%44 $5))) (%39 ((%45 $1) $3)))))
       (((($6 $5) $4) $3) ((%51 $2) $0)))) ((%38 ((%12 ((%12 (%39 ((%40 $3)
       $4))) ((%41 $3) (%42 $5)))) ((%12 ((%41 (%43 $2)) (%44 $5))) ((%45
       $1) $3)))) (((($6 $5) $4) $3) ((%51 $2) $0)))))) (((($6 $5) $4) $3)
       ((%51 $2) ((%22 $1) $0)))))))))))))))))) (%0 (\%80. (%30 (\%81. (%2
       (\%82. (%36 (\%83. (((($4 $3) $2) $1) $0))))))))))))`)
  val followRuleEq1 =
    DT(["MK_THM"], [],
       `(%0 (\%1. (%30 (\%35. (%2 (\%3. (%36 (\%84. ((%38 ((%41 %85)
       ((((%76 $3) $2) $1) $0))) ((%41 %85) ((%5 $3) $1)))))))))))`)
  val followSetEq1 =
    DT(["DISK_THM", "MK_THM"], [],
       `(%0 (\%1. (%2 (\%3. ((%38 ((%41 %85) ((%77 $1) $0))) ((%41 %85)
       ((%5 $1) $0)))))))`)
  end
  val _ = DB.bindl "followSetDef"
  [("followSet_def",followSet_def,DB.Def),
   ("followRuleML_defn_tupled_primitive_def",
    followRuleML_defn_tupled_primitive_def,
    DB.Def),
   ("followRuleML_defn_curried_def",followRuleML_defn_curried_def,DB.Def),
   ("followSetML_def",followSetML_def,DB.Def),
   ("followRuleML",followRuleML,DB.Thm),
   ("followRuleML_ind",followRuleML_ind,DB.Thm),
   ("followRuleEq1",followRuleEq1,DB.Thm),
   ("followSetEq1",followSetEq1,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("firstSetDefTheory.firstSetDef_grammars",
                          firstSetDefTheory.firstSetDef_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "followSet")
        {Name = "followSet", Thy = "followSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "followRuleML_defn_tupled")
        {Name = "followRuleML_defn_tupled", Thy = "followSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "followRuleML")
        {Name = "followRuleML", Thy = "followSetDef"}
  val _ = update_grms
       (temp_overload_on_by_nametype "followSetML")
        {Name = "followSetML", Thy = "followSetDef"}
  val followSetDef_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [followSet_def];  
  
  val _ = computeLib.add_funs [followSetML_def];
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
