structure containerLemmasTheory :> containerLemmasTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading containerLemmasTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open containerTheory
  in end;
  val _ = Theory.link_parents
          ("containerLemmas",
          Arbnum.fromString "1203550984",
          Arbnum.fromString "18625")
          [("container",
           Arbnum.fromString "1201303259",
           Arbnum.fromString "610400")];
  val _ = Theory.incorporate_types "containerLemmas" [];
  val _ = Theory.incorporate_consts "containerLemmas" [];
  
  local
  val share_table = Vector.fromList
  [C"!" "bool" (((alpha --> bool) --> bool)), V"e" (alpha),
   C"!" "bool" (((T"list" "list" [alpha] --> bool) --> bool)),
   V"l" (T"list" "list" [alpha]), C"=" "min" ((bool --> (bool --> bool))),
   C"MEM" "list" ((alpha --> (T"list" "list" [alpha] --> bool))),
   C"IN" "bool" ((alpha --> ((alpha --> bool) --> bool))),
   C"LIST_TO_SET" "list" ((T"list" "list" [alpha] --> (alpha --> bool))),
   V"l1" (T"list" "list" [alpha]), V"l2" (T"list" "list" [alpha]),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"SUBSET" "pred_set"
    (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C">=" "arithmetic" ((T"num" "num" [] --> (T"num" "num" [] --> bool))),
   C"LENGTH" "list" ((T"list" "list" [alpha] --> T"num" "num" [])),
   C"CARD" "pred_set" (((alpha --> bool) --> T"num" "num" [])),
   C"!" "bool" ((((alpha --> bool) --> bool) --> bool)),
   V"p" ((alpha --> bool)),
   C"=" "min" (((alpha --> bool) --> ((alpha --> bool) --> bool))),
   C"FILTER" "list"
    (((alpha --> bool) -->
      (T"list" "list" [alpha] --> T"list" "list" [alpha]))),
   C"GSPEC" "pred_set"
    (((alpha --> T"prod" "pair" [alpha, bool]) --> (alpha --> bool))),
   V"x" (alpha),
   C"," "pair" ((alpha --> (bool --> T"prod" "pair" [alpha, bool]))),
   C"/\\" "bool" ((bool --> (bool --> bool)))]
  val DT = Thm.disk_thm share_table
  in
  val mem_in =
    DT(["DISK_THM"], [],
       `(%0 (\%1. (%2 (\%3. ((%4 ((%5 $1) $0)) ((%6 $1) (%7 $0)))))))`)
  val mem_subset =
    DT(["DISK_THM"], [],
       `(%2 (\%8. (%2 (\%9. ((%10 (%0 (\%1. ((%10 ((%5 $0) $2)) ((%5 $0)
       $1))))) ((%11 (%7 $1)) (%7 $0)))))))`)
  val len_card =
    DT(["DISK_THM"], [], `(%2 (\%3. ((%12 (%13 $0)) (%14 (%7 $0)))))`)
  val filter_seteq =
    DT(["DISK_THM"], [],
       `(%15 (\%16. (%2 (\%3. ((%17 (%7 ((%18 $1) $0))) (%19 (\%20. ((%21
       $0) ((%22 ($2 $0)) ((%5 $0) $1))))))))))`)
  end
  val _ = DB.bindl "containerLemmas"
  [("mem_in",mem_in,DB.Thm), ("mem_subset",mem_subset,DB.Thm),
   ("len_card",len_card,DB.Thm), ("filter_seteq",filter_seteq,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("containerTheory.container_grammars",
                          containerTheory.container_grammars)]
  val _ = List.app (update_grms reveal) []
  
  val containerLemmas_grammars = Parse.current_lgrms()
  end
  
  
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
