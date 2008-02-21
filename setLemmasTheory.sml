structure setLemmasTheory :> setLemmasTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading setLemmasTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open pred_setTheory stringTheory
  in end;
  val _ = Theory.link_parents
          ("setLemmas",
          Arbnum.fromString "1203551050",
          Arbnum.fromString "695895")
          [("string",
           Arbnum.fromString "1201303028",
           Arbnum.fromString "222060"),
           ("pred_set",
           Arbnum.fromString "1201303045",
           Arbnum.fromString "278600")];
  val _ = Theory.incorporate_types "setLemmas" [];
  val _ = Theory.incorporate_consts "setLemmas" [];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"s" ((alpha --> bool)), C"==>" "min" ((bool --> (bool --> bool))),
   C"FINITE" "pred_set" (((alpha --> bool) --> bool)),
   C"!" "bool" ((((alpha --> T"num" "num" []) --> bool) --> bool)),
   V"f" ((alpha --> T"num" "num" [])),
   C"<" "prim_rec" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"0" "num" (T"num" "num" []),
   C"SUM_IMAGE" "pred_set"
    (((alpha --> T"num" "num" []) -->
      ((alpha --> bool) --> T"num" "num" []))),
   C"?" "bool" (((alpha --> bool) --> bool)), V"e" (alpha),
   C"/\\" "bool" ((bool --> (bool --> bool))),
   C"IN" "bool" ((alpha --> ((alpha --> bool) --> bool))),
   C"<=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"n" (T"num" "num" []), C"!" "bool" (((alpha --> bool) --> bool)),
   C"=" "min" (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"INTER" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> (alpha --> bool)))),
   C"INSERT" "pred_set"
    ((alpha --> ((alpha --> bool) --> (alpha --> bool)))),
   C"EMPTY" "pred_set" ((alpha --> bool)), C"~" "bool" ((bool --> bool)),
   C"=" "min" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   V"s1" ((alpha --> bool)), V"s2" ((alpha --> bool)),
   C"DIFF" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> (alpha --> bool)))),
   C"-" "arithmetic"
    ((T"num" "num" [] --> (T"num" "num" [] --> T"num" "num" []))),
   C">" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"CARD" "pred_set" (((alpha --> bool) --> T"num" "num" [])),
   C"SUBSET" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   V"t" ((alpha --> bool)),
   C"PSUBSET" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"UNION" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> (alpha --> bool)))),
   V"x" (alpha),
   C"GSPEC" "pred_set"
    (((alpha --> T"prod" "pair" [alpha, bool]) --> (alpha --> bool))),
   C"," "pair" ((alpha --> (bool --> T"prod" "pair" [alpha, bool]))),
   C"LIST_TO_SET" "list" ((T"list" "list" [alpha] --> (alpha --> bool))),
   V"l" (T"list" "list" [alpha]),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool)))]
  val DT = Thm.disk_thm share_table
  in
  val set_l1 =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (%3 $0)) (%4 (\%5. ((%2 ((%6 %7) ((%8 $0) $1))) (%9
       (\%10. ((%11 ((%12 $0) $2)) ((%6 %7) ($1 $0)))))))))))`)
  val set_l2 =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (%3 $0)) (%4 (\%5. ((%2 (%9 (\%10. ((%11 ((%12 $0)
       $2)) ((%6 %7) ($1 $0)))))) ((%6 %7) ((%8 $0) $1))))))))`)
  val set_l3 =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (%3 $0)) (%4 (\%5. ((%2 (%9 (\%10. ((%11 ((%12 $0)
       $2)) ((%13 %14) ($1 $0)))))) ((%13 %14) ((%8 $0) $1))))))))`)
  val inter_l1 =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%15 (\%10. ((%2 ((%12 $0) $1)) ((%16 ((%17 $1) ((%18 $0)
       %19))) ((%18 $0) %19)))))))`)
  val inter_l2 =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%15 (\%10. ((%2 (%20 ((%12 $0) $1))) ((%16 ((%17 $1)
       ((%18 $0) %19))) %19))))))`)
  val set_l4 =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (%3 $0)) (%4 (\%5. ((%2 ((%21 ((%8 $0) $1)) %7))
       (%15 (\%10. ((%2 ((%12 $0) $2)) ((%21 ($1 $0)) %7))))))))))`)
  val f_diff1 =
    DT(["DISK_THM"], [],
       `(%0 (\%22. ((%2 (%3 $0)) (%4 (\%5. (%0 (\%23. ((%13 ((%8 $1) ((%17
       $2) $0))) ((%8 $1) $2)))))))))`)
  val f_diff =
    DT(["DISK_THM"], [],
       `(%0 (\%22. ((%2 (%3 $0)) (%4 (\%5. (%0 (\%23. ((%21 ((%8 $1) ((%24
       $2) $0))) ((%25 ((%8 $1) $2)) ((%8 $1) ((%17 $2) $0)))))))))))`)
  val set_neq =
    DT(["DISK_THM"], [],
       `(%0 (\%23. ((%2 (%3 $0)) (%0 (\%22. ((%2 (%3 $0)) ((%2 ((%26 (%27
       $0)) (%27 $1))) (%9 (\%10. ((%11 (%20 ((%12 $0) $2))) ((%12 $0)
       $1)))))))))))`)
  val insert_absorption =
    DT(["DISK_THM"], [],
       `(%0 (\%1. ((%2 (%3 $0)) ((%2 ((%12 %10) $0)) ((%16 ((%18 %10) $0))
       $0)))))`)
  val inter_card_less =
    DT(["DISK_THM"], [],
       `(%0 (\%22. ((%2 (%3 $0)) ((%2 ((%12 %10) $0)) ((%2 (%20 ((%12 %10)
       %23))) ((%26 ((%25 (%27 $0)) (%27 ((%17 $0) %23)))) %7))))))`)
  val subset_inter =
    DT(["DISK_THM"], [],
       `(%0 (\%23. ((%2 (%3 $0)) (%0 (\%22. ((%2 ((%28 $0) $1)) (%0 (\%29.
       ((%28 ((%17 $1) $0)) ((%17 $2) $0))))))))))`)
  val card_same_inter =
    DT(["DISK_THM"], [],
       `(%0 (\%23. ((%2 (%3 $0)) ((%2 ((%30 %22) $0)) ((%2 (%20 ((%12 %10)
       %22))) ((%2 ((%12 %10) $0)) ((%2 ((%12 %10) %29)) ((%6 (%27 ((%17
       %22) %29))) (%27 ((%17 $0) %29))))))))))`)
  val insert_union =
    DT(["DISK_THM"], [],
       `((%16 ((%31 %22) ((%18 %32) %23))) ((%18 %32) ((%31 %22) %23)))`)
  val setc_mem_in =
    DT(["DISK_THM"], [],
       `((%16 (%33 (\%10. ((%34 $0) ((%12 $0) (%35 %36)))))) (%33 (\%10.
       ((%34 $0) ((%37 $0) %36)))))`)
  val not_in_inter =
    DT(["DISK_THM"], [],
       `(%0 (\%22. ((%2 (%3 $0)) ((%2 ((%12 %10) $0)) ((%2 (%20 ((%12 %10)
       %23))) (%20 ((%12 %10) ((%17 $0) %23))))))))`)
  end
  val _ = DB.bindl "setLemmas"
  [("set_l1",set_l1,DB.Thm), ("set_l2",set_l2,DB.Thm),
   ("set_l3",set_l3,DB.Thm), ("inter_l1",inter_l1,DB.Thm),
   ("inter_l2",inter_l2,DB.Thm), ("set_l4",set_l4,DB.Thm),
   ("f_diff1",f_diff1,DB.Thm), ("f_diff",f_diff,DB.Thm),
   ("set_neq",set_neq,DB.Thm),
   ("insert_absorption",insert_absorption,DB.Thm),
   ("inter_card_less",inter_card_less,DB.Thm),
   ("subset_inter",subset_inter,DB.Thm),
   ("card_same_inter",card_same_inter,DB.Thm),
   ("insert_union",insert_union,DB.Thm),
   ("setc_mem_in",setc_mem_in,DB.Thm),
   ("not_in_inter",not_in_inter,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("stringTheory.string_grammars",
                          stringTheory.string_grammars),
                         ("pred_setTheory.pred_set_grammars",
                          pred_setTheory.pred_set_grammars)]
  val _ = List.app (update_grms reveal) []
  
  val setLemmas_grammars = Parse.current_lgrms()
  end
  
  
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
