structure boolLemmasTheory :> boolLemmasTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading boolLemmasTheory ... " else ()
  open Type Term Thm
  infixr -->
  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  
  (*  Parents *)
  local open containerTheory stringTheory
  in end;
  val _ = Theory.link_parents
          ("boolLemmas",
          Arbnum.fromString "1203550974",
          Arbnum.fromString "56827")
          [("container",
           Arbnum.fromString "1201303259",
           Arbnum.fromString "610400"),
           ("string",
           Arbnum.fromString "1201303028",
           Arbnum.fromString "222060")];
  val _ = Theory.incorporate_types "boolLemmas" [];
  val _ = Theory.incorporate_consts "boolLemmas" [];
  
  local
  val share_table = Vector.fromList
  [C"=" "min" ((bool --> (bool --> bool))),
   C"=" "min"
    ((T"option" "option" [alpha] -->
      (T"option" "option" [alpha] --> bool))),
   C"COND" "bool"
    ((bool -->
      (T"option" "option" [alpha] -->
       (T"option" "option" [alpha] --> T"option" "option" [alpha])))),
   V"p" (bool), C"SOME" "option" ((alpha --> T"option" "option" [alpha])),
   V"x" (alpha), C"NONE" "option" (T"option" "option" [alpha]),
   V"x'" (alpha), C"/\\" "bool" ((bool --> (bool --> bool))),
   C"=" "min" ((alpha --> (alpha --> bool))),
   C"?" "bool" (((alpha --> bool) --> bool)),
   C"?" "bool" (((T"option" "option" [alpha] --> bool) --> bool)),
   V"p'" (T"option" "option" [alpha]),
   C"option_case" "option"
    ((T"option" "option" [alpha] -->
      ((beta --> T"option" "option" [alpha]) -->
       (T"option" "option" [beta] --> T"option" "option" [alpha])))),
   V"y" (beta), V"f" ((beta --> T"option" "option" [alpha])),
   V"x" (T"option" "option" [beta]), V"z" (alpha),
   C"?" "bool" (((beta --> bool) --> bool)), V"a" (beta),
   C"=" "min"
    ((T"option" "option" [beta] --> (T"option" "option" [beta] --> bool))),
   C"SOME" "option" ((beta --> T"option" "option" [beta])),
   C"list_case" "list"
    ((T"option" "option" [alpha] -->
      ((beta --> (T"list" "list" [beta] --> T"option" "option" [alpha]))
       --> (T"list" "list" [beta] --> T"option" "option" [alpha])))),
   V"h" (beta), V"t" (T"list" "list" [beta]),
   V"f"
    ((beta --> (T"list" "list" [beta] --> T"option" "option" [alpha]))),
   V"x" (T"list" "list" [beta]), V"i" (beta),
   C"?" "bool" (((T"list" "list" [beta] --> bool) --> bool)),
   V"j" (T"list" "list" [beta]),
   C"=" "min"
    ((T"list" "list" [beta] --> (T"list" "list" [beta] --> bool))),
   C"CONS" "list"
    ((beta --> (T"list" "list" [beta] --> T"list" "list" [beta]))),
   V"y" (T"option" "option" [alpha]),
   C"NIL" "list" (T"list" "list" [beta]),
   C"!" "bool" (((T"option" "option" [alpha] --> bool) --> bool)),
   V"f" (T"option" "option" [alpha]),
   C"==>" "min" ((bool --> (bool --> bool))),
   C"~" "bool" ((bool --> bool)),
   C"THE" "option" ((T"option" "option" [alpha] --> alpha)),
   C"FINITE" "pred_set" (((alpha --> bool) --> bool)),
   C"GSPEC" "pred_set"
    (((alpha --> T"prod" "pair" [alpha, bool]) --> (alpha --> bool))),
   C"," "pair" ((alpha --> (bool --> T"prod" "pair" [alpha, bool]))),
   V"P" ((alpha --> bool)),
   C"FINITE" "pred_set" (((T"list" "list" [alpha] --> bool) --> bool)),
   C"GSPEC" "pred_set"
    (((T"list" "list" [alpha] -->
       T"prod" "pair" [T"list" "list" [alpha], bool]) -->
      (T"list" "list" [alpha] --> bool))), V"l" (T"list" "list" [alpha]),
   C"," "pair"
    ((T"list" "list" [alpha] -->
      (bool --> T"prod" "pair" [T"list" "list" [alpha], bool]))),
   C"EVERY" "list"
    (((alpha --> bool) --> (T"list" "list" [alpha] --> bool))),
   C"ALL_DISTINCT" "list" ((T"list" "list" [alpha] --> bool))]
  val DT = Thm.disk_thm share_table
  in
  val if_rw_SOMEeqSOME =
    DT(["DISK_THM"], [],
       `((%0 ((%1 (((%2 %3) (%4 %5)) %6)) (%4 %7))) ((%8 ((%9 %5) %7))
       %3))`)
  val if_rw_SOME =
    DT(["DISK_THM"], [],
       `(%10 (\%7. (%11 (\%12. ((%0 ((%1 (%4 $1)) (((%2 %3) %6) $0))) ((%1
       $0) (%4 $1)))))))`)
  val option_case_rwt =
    DT(["DISK_THM"], [],
       `((%0 ((%1 (((%13 %6) (\%14. (%15 $0))) %16)) (%4 %17))) (%18 (\%19.
       ((%8 ((%20 %16) (%21 $0))) ((%1 (%15 $0)) (%4 %17))))))`)
  val list_case_rwt =
    DT(["DISK_THM"], [],
       `((%8 ((%0 ((%1 (((%22 %6) (\%23. (\%24. ((%25 $1) $0)))) %26)) (%4
       %17))) (%18 (\%27. (%28 (\%29. ((%8 ((%30 %26) ((%31 $1) $0))) ((%1
       ((%25 $1) $0)) (%4 %17))))))))) ((%0 ((%1 (((%22 %32) (\%23. (\%24.
       %6))) %26)) (%4 %17))) ((%8 ((%30 %26) %33)) ((%1 %32) (%4
       %17)))))`)
  val option_r1 =
    DT(["DISK_THM"], [],
       `(%34 (\%35. ((%36 (%37 ((%1 $0) %6))) ((%36 ((%9 %5) (%38 $0)))
       ((%1 (%4 %5)) $0)))))`)
  val lemma =
    DT(["DISK_THM"], [],
       `((%36 (%39 (%40 (\%5. ((%41 $0) (%42 $0)))))) (%43 (%44 (\%45.
       ((%46 $0) ((%8 ((%47 %42) $0)) (%48 $0)))))))`)
  val setc_flem =
    DT(["DISK_THM"], [],
       `((%36 (%39 %42)) (%43 (%44 (\%45. ((%46 $0) ((%8 ((%47 %42) $0))
       (%48 $0)))))))`)
  end
  val _ = DB.bindl "boolLemmas"
  [("if_rw_SOMEeqSOME",if_rw_SOMEeqSOME,DB.Thm),
   ("if_rw_SOME",if_rw_SOME,DB.Thm),
   ("option_case_rwt",option_case_rwt,DB.Thm),
   ("list_case_rwt",list_case_rwt,DB.Thm), ("option_r1",option_r1,DB.Thm),
   ("lemma",lemma,DB.Thm), ("setc_flem",setc_flem,DB.Thm)]
  
  local open Portable GrammarSpecials Parse
  in
  val _ = mk_local_grms [("containerTheory.container_grammars",
                          containerTheory.container_grammars),
                         ("stringTheory.string_grammars",
                          stringTheory.string_grammars)]
  val _ = List.app (update_grms reveal) []
  
  val boolLemmas_grammars = Parse.current_lgrms()
  end
  
  
  val _ = if !Globals.print_thy_loads then print "done\n" else ()

end
