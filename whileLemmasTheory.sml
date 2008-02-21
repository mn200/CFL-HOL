structure whileLemmasTheory :> whileLemmasTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading whileLemmasTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open boolLemmasTheory
  in end;
  val _ = Theory.link_parents
          ("whileLemmas",
          Arbnum.fromString "1203551036",
          Arbnum.fromString "20137")
          [("boolLemmas",
           Arbnum.fromString "1203550974",
           Arbnum.fromString "56827")];
  val _ = Theory.incorporate_types "whileLemmas" [];
  val _ = Theory.incorporate_consts "whileLemmas"
     [("owhile",
       (((alpha --> bool) -->
         ((alpha --> alpha) --> (alpha --> T"option" "option" [alpha]))))),
      ("mwhile",
       (((alpha --> bool) -->
         ((alpha --> T"option" "option" [alpha]) -->
          (T"option" "option" [alpha] -->
           T"option" "option" [T"option" "option" [alpha]]))))),
      ("terminates",
       ((T"prod" "pair"
          [(alpha --> bool), T"prod" "pair" [(alpha --> alpha), alpha]] -->
         bool)))];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"C" ((alpha --> bool)),
   C"!" "bool" ((((alpha --> alpha) --> bool) --> bool)),
   V"f" ((alpha --> alpha)), C"!" "bool" (((alpha --> bool) --> bool)),
   V"s" (alpha),
   C"=" "min"
    ((T"option" "option" [alpha] -->
      (T"option" "option" [alpha] --> bool))),
   C"owhile" "whileLemmas"
    (((alpha --> bool) -->
      ((alpha --> alpha) --> (alpha --> T"option" "option" [alpha])))),
   C"COND" "bool"
    ((bool -->
      (T"option" "option" [alpha] -->
       (T"option" "option" [alpha] --> T"option" "option" [alpha])))),
   C"?" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"n" (T"num" "num" []), C"~" "bool" ((bool --> bool)),
   C"FUNPOW" "arithmetic"
    (((alpha --> alpha) --> (T"num" "num" [] --> (alpha --> alpha)))),
   C"SOME" "option" ((alpha --> T"option" "option" [alpha])),
   C"LEAST" "while" (((T"num" "num" [] --> bool) --> T"num" "num" [])),
   C"NONE" "option" (T"option" "option" [alpha]),
   C"=" "min" ((bool --> (bool --> bool))),
   C"terminates" "whileLemmas"
    ((T"prod" "pair"
       [(alpha --> bool), T"prod" "pair" [(alpha --> alpha), alpha]] -->
      bool)),
   C"," "pair"
    (((alpha --> bool) -->
      (T"prod" "pair" [(alpha --> alpha), alpha] -->
       T"prod" "pair"
        [(alpha --> bool), T"prod" "pair" [(alpha --> alpha), alpha]]))),
   C"," "pair"
    (((alpha --> alpha) -->
      (alpha --> T"prod" "pair" [(alpha --> alpha), alpha]))),
   V"P" ((alpha --> bool)),
   C"!" "bool"
    ((((alpha --> T"option" "option" [alpha]) --> bool) --> bool)),
   V"f" ((alpha --> T"option" "option" [alpha])),
   C"=" "min"
    (((T"option" "option" [alpha] -->
       T"option" "option" [T"option" "option" [alpha]]) -->
      ((T"option" "option" [alpha] -->
        T"option" "option" [T"option" "option" [alpha]]) --> bool))),
   C"mwhile" "whileLemmas"
    (((alpha --> bool) -->
      ((alpha --> T"option" "option" [alpha]) -->
       (T"option" "option" [alpha] -->
        T"option" "option" [T"option" "option" [alpha]])))),
   C"owhile" "whileLemmas"
    (((T"option" "option" [alpha] --> bool) -->
      ((T"option" "option" [alpha] --> T"option" "option" [alpha]) -->
       (T"option" "option" [alpha] -->
        T"option" "option" [T"option" "option" [alpha]])))),
   V"opt" (T"option" "option" [alpha]),
   C"option_case" "option"
    ((bool -->
      ((alpha --> bool) --> (T"option" "option" [alpha] --> bool)))),
   C"T" "bool" (bool),
   C"option_case" "option"
    ((T"option" "option" [alpha] -->
      ((alpha --> T"option" "option" [alpha]) -->
       (T"option" "option" [alpha] --> T"option" "option" [alpha])))),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"/\\" "bool" ((bool --> (bool --> bool))), V"x" (alpha),
   C"?" "bool" (((alpha --> bool) --> bool)), V"s'" (alpha),
   C"!" "bool" (((T"num" "num" [] --> bool) --> bool)),
   V"m" (T"num" "num" []),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"!" "bool" (((T"option" "option" [alpha] --> bool) --> bool)),
   V"s" (T"option" "option" [alpha]),
   C"=" "min"
    ((T"option" "option" [T"option" "option" [alpha]] -->
      (T"option" "option" [T"option" "option" [alpha]] --> bool))),
   C"NONE" "option" (T"option" "option" [T"option" "option" [alpha]]),
   C"terminates" "whileLemmas"
    ((T"prod" "pair"
       [(T"option" "option" [alpha] --> bool),
        T"prod" "pair"
         [(T"option" "option" [alpha] --> T"option" "option" [alpha]),
          T"option" "option" [alpha]]] --> bool)),
   C"," "pair"
    (((T"option" "option" [alpha] --> bool) -->
      (T"prod" "pair"
        [(T"option" "option" [alpha] --> T"option" "option" [alpha]),
         T"option" "option" [alpha]] -->
       T"prod" "pair"
        [(T"option" "option" [alpha] --> bool),
         T"prod" "pair"
          [(T"option" "option" [alpha] --> T"option" "option" [alpha]),
           T"option" "option" [alpha]]]))),
   C"," "pair"
    (((T"option" "option" [alpha] --> T"option" "option" [alpha]) -->
      (T"option" "option" [alpha] -->
       T"prod" "pair"
        [(T"option" "option" [alpha] --> T"option" "option" [alpha]),
         T"option" "option" [alpha]]))),
   C"?" "bool" (((T"option" "option" [alpha] --> bool) --> bool)),
   V"s'" (T"option" "option" [alpha]),
   C"SOME" "option"
    ((T"option" "option" [alpha] -->
      T"option" "option" [T"option" "option" [alpha]])), V"x'" (alpha)]
  val DT = Thm.disk_thm share_table
  in
  val owhile_def =
    DT([], [],
       `(%0 (\%1. (%2 (\%3. (%4 (\%5. ((%6 (((%7 $2) $1) $0)) (((%8 (%9
       (\%10. (%11 ($3 (((%12 $2) $0) $1)))))) (%13 (((%12 $1) (%14 (\%10.
       (%11 ($3 (((%12 $2) $0) $1)))))) $0))) %15))))))))`)
  val terminates_def =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%2 (\%3. (%4 (\%5. ((%16 (%17 ((%18 $2) ((%19 $1) $0))))
       (%9 (\%10. (%11 ($3 (((%12 $2) $0) $1))))))))))))`)
  val mwhile_def =
    DT([], [],
       `(%0 (\%20. (%21 (\%22. ((%23 ((%24 $1) $0)) ((%25 (\%26. (((%27
       %28) (\%5. ($3 $0))) $0))) (\%26. (((%29 %15) (\%5. ($2 $0)))
       $0))))))))`)
  val owhile_thm =
    DT(["DISK_THM"], [],
       `((%6 (((%7 %1) %3) %5)) (((%8 (%1 %5)) (((%7 %1) %3) (%3 %5))) (%13
       %5)))`)
  val owhile_EQ_NONE =
    DT(["DISK_THM"], [],
       `((%16 ((%6 (((%7 %1) %3) %5)) %15)) (%11 (%17 ((%18 %1) ((%19 %3)
       %5)))))`)
  val obua_induct2 =
    DT(["DISK_THM"], [],
       `((%30 ((%31 (%17 ((%18 %1) ((%19 %3) %5)))) (%4 (\%32. ((%30 ((%30
       (%1 $0)) (%20 (%3 $0)))) (%20 $0)))))) (%20 %5))`)
  val owhile_EQ_SOME =
    DT(["DISK_THM"], [],
       `((%16 (%33 (\%34. ((%6 (((%7 %1) %3) %5)) (%13 $0))))) (%17 ((%18
       %1) ((%19 %3) %5))))`)
  val owhileEndCond =
    DT(["DISK_THM"], [],
       `(%4 (\%34. ((%30 ((%6 (((%7 %1) %3) %5)) (%13 $0))) (%11 (%1
       $0)))))`)
  val nthStateProp =
    DT(["DISK_THM"], [],
       `((%30 (%4 (\%32. ((%30 ((%31 (%20 $0)) (%1 $0))) (%20 (%3 $0))))))
       (%35 (\%10. (%4 (\%5. ((%30 ((%31 (%20 $0)) (%35 (\%36. ((%30 ((%37
       $0) $2)) (%1 (((%12 %3) $0) $1))))))) (%20 (((%12 %3) $1)
       $0))))))))`)
  val owhileEndState =
    DT(["DISK_THM"], [],
       `((%30 ((%31 ((%6 (((%7 %1) %3) %5)) (%13 %34))) ((%31 (%4 (\%32.
       ((%30 ((%31 (%20 $0)) (%1 $0))) (%20 (%3 $0)))))) (%20 %5)))) (%20
       %34))`)
  val mwhile_EQ_NONE =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%21 (\%22. (%38 (\%39. ((%16 ((%40 (((%24 $2) $1) $0))
       %41)) (%11 (%42 ((%43 (\%26. (((%27 %28) (\%32. ($4 $0))) $0)))
       ((%44 (\%26. (((%29 %15) (\%32. ($3 $0))) $0))) $0)))))))))))`)
  val mwhile_EQ_SOME =
    DT(["DISK_THM"], [],
       `((%16 (%45 (\%46. ((%40 (((%24 %1) %22) %39)) (%47 $0))))) (%42
       ((%43 (\%26. (((%27 %28) (\%32. (%1 $0))) $0))) ((%44 (\%26. (((%29
       %15) (\%32. (%22 $0))) $0))) %39))))`)
  val mwhileEndCond =
    DT(["DISK_THM"], [],
       `((%30 ((%40 (((%24 %1) %22) %39)) (%47 (%13 %34)))) (%11 (%1
       %34)))`)
  val mwhileEndState =
    DT(["DISK_THM"], [],
       `((%30 ((%31 ((%40 (((%24 %1) %22) (%13 %5))) (%47 (%13 %34))))
       ((%31 (%4 (\%32. (%4 (\%48. ((%30 ((%31 (%20 $1)) ((%31 (%1 $1))
       ((%6 (%22 $1)) (%13 $0))))) (%20 $0))))))) (%20 %5)))) (%20 %34))`)
  end
  val _ = DB.bindl "whileLemmas"
  [("owhile_def",owhile_def,DB.Def),
   ("terminates_def",terminates_def,DB.Def),
   ("mwhile_def",mwhile_def,DB.Def), ("owhile_thm",owhile_thm,DB.Thm),
   ("owhile_EQ_NONE",owhile_EQ_NONE,DB.Thm),
   ("obua_induct2",obua_induct2,DB.Thm),
   ("owhile_EQ_SOME",owhile_EQ_SOME,DB.Thm),
   ("owhileEndCond",owhileEndCond,DB.Thm),
   ("nthStateProp",nthStateProp,DB.Thm),
   ("owhileEndState",owhileEndState,DB.Thm),
   ("mwhile_EQ_NONE",mwhile_EQ_NONE,DB.Thm),
   ("mwhile_EQ_SOME",mwhile_EQ_SOME,DB.Thm),
   ("mwhileEndCond",mwhileEndCond,DB.Thm),
   ("mwhileEndState",mwhileEndState,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("boolLemmasTheory.boolLemmas_grammars",
                          boolLemmasTheory.boolLemmas_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (temp_overload_on_by_nametype "owhile")
        {Name = "owhile", Thy = "whileLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "terminates")
        {Name = "terminates", Thy = "whileLemmas"}
  val _ = update_grms
       (temp_overload_on_by_nametype "mwhile")
        {Name = "mwhile", Thy = "whileLemmas"}
  val whileLemmas_grammars = Parse.current_lgrms()
  end
  
  
  
  
  val _ = computeLib.add_funs [owhile_def];  
  
  val _ = computeLib.add_funs [terminates_def];  
  
  val _ = computeLib.add_funs [mwhile_def];  
  
  val _ = 
     let fun dconst thy c = 
           let val {Name,Ty,...} = Term.dest_thy_const c
           in (c,(thy,Name,Ty))
           end
         val clist = map ConstMapML.iconst
           [([],"owhile","whileLemmas"), ([],"mwhile","whileLemmas")]
     in 
       List.app ConstMapML.prim_insert (map (dconst "whileLemmas") clist)
     end
  
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
