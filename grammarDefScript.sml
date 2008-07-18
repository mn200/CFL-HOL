(* A theory about regular expressions *)

open HolKernel boolLib bossLib Parse BasicProvers

open stringTheory relationTheory listTheory arithmeticTheory Defn
containerTheory pred_setTheory

open pred_setTheory listLemmasTheory regexpTheory
containerLemmasTheory setLemmasTheory


val _ = new_theory "grammarDef";

(* 14/05/07 AB *)


(* Theory of context free grammar. Based on Chapter 4, Hopcroft & Ullman *)
(* working version using HOL definitions. *)
(* Second version making a grammar without specifying terms n non-terms *)
(* Type definitions *)

(* correct definition of rgr + added thms *)

(* finished unit productions *)
(* add property based deifinitions of CNF *)
(* ADD a constraint on rules being a finite set *)

(* cnf done for replacement of terminals *)
(* NOW handle nonterminals *)

val _ = overload_on ("set", ``LIST_TO_SET``);

(* e.g. S -> E * E becomes (Node S [E, *, E]) *)
val _ = Hol_datatype `rule = rule of string => symbol list`; (*  # symbol list`;*)

(* ?? verifying whether the spec of the grammar is consistent *)
(* grammar = (V, T, P, S) *)
val _ = Hol_datatype `grammar = G of rule list => string`;

val ruleRhs = Define `ruleRhs (rule l r) = r`

val ruleLhs = Define `ruleLhs (rule l r) = l`


val getRules = Define `
   (getRules sym [] = []) /\
   (getRules sym ((rule l r)::rs) = if (sym = l) then
                                      rule l r :: getRules sym rs
                                    else getRules sym rs)
`


val rhsWithSym = Define `(rhsWithSym sym [] = []) /\
 (rhsWithSym sym ((rule l r)::rst) = if MEM sym r then (r::rhsWithSym sym rst) else rhsWithSym sym rst)`

val rulesWithSymInRhs = Define `(rulesWithSymInRhs sym [] = []) /\
 (rulesWithSymInRhs sym ((rule l r)::rst) = if MEM sym r then ((l, breakAtElem sym r)::rulesWithSymInRhs sym rst) else rulesWithSymInRhs sym rst)`


val lhsWithLastSym = Define `
  (lhsWithLastSym sym [] = []) /\
  (lhsWithLastSym sym ((rule l [])::rs) = rmDupes (lhsWithLastSym sym rs)) /\
  (lhsWithLastSym sym ((rule l r)::rs) =
        if (LAST r =  sym) then rmDupes ((NTS l) :: lhsWithLastSym sym rs)
        else rmDupes (lhsWithLastSym sym rs))
`

val last_l1 = prove(
  ``!sym l r. ~(lhsWithLastSym  sym [rule l r] = []) ==> (?pfx.pfx++[sym]=r)``,
  REPEAT GEN_TAC THEN Cases_on `r` THEN
  SRW_TAC [][lhsWithLastSym, rmDupes] THEN
  Q.EXISTS_TAC `FRONT (h::t)` THEN
  SRW_TAC [][APPEND_FRONT_LAST]);

val lwls_r1 = store_thm ("lwls_r1",
`` ~(lhsWithLastSym sym (rule s l::rs)=[]) ==> (~(lhsWithLastSym sym [rule s l] = []) \/ ~(lhsWithLastSym sym rs = []))``,
SRW_TAC [] [] THEN
Cases_on `l` THENL[
FULL_SIMP_TAC (srw_ss()) [lhsWithLastSym] THEN
METIS_TAC [rmDupes],
METIS_TAC [rmDupes,lhsWithLastSym]])


val notNullLhsLastSym = store_thm ("notNullLhsLastSym",
``!sym rs.~(lhsWithLastSym sym rs = []) ==> (?l pfx.MEM (rule l (pfx++[sym])) rs)``,
SRW_TAC [] [] THEN
Induct_on `rs` THEN
SRW_TAC [] [lhsWithLastSym] THEN

SRW_TAC [] [] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
` ~(lhsWithLastSym sym (rule s l::rs)=[]) ==> (~(lhsWithLastSym sym [rule s l] = []) \/ ~(lhsWithLastSym sym rs = []))` by METIS_TAC [lwls_r1] THEN
RES_TAC  THEN
`~(lhsWithLastSym  sym [rule s l] = []) ==> (?pfx.l=pfx++[sym])` by METIS_TAC [last_l1] THEN
METIS_TAC [])

val rule_terminals = Define
`rule_terminals (rule l r) = { tmnl | isTmnlSym tmnl /\ MEM tmnl r }`

val rule_nonterminals = Define`
  rule_nonterminals (rule l r) = NTS l INSERT { nt | isNonTmnlSym nt /\ MEM nt r }
`

val is_word  = Define `is_word w = EVERY isTmnlSym w`

val rules = Define`rules (G p s) = p`

val startSym = Define `startSym (G p s) = s`;


val terminals = Define `terminals (G p s) = BIGUNION (IMAGE rule_terminals (LIST_TO_SET p))`

val nonTerminals = Define `
  nonTerminals (G p s) =
      NTS s INSERT BIGUNION (IMAGE rule_nonterminals (LIST_TO_SET p))
`

val nonTerminalsML =  Define `
  (nonTerminalsML (G [] s) = {NTS s}) /\
  (nonTerminalsML (G (rule l r::rs) s) =
          LIST_TO_SET (FILTER isNonTmnlSym (NTS l :: r)) UNION
          nonTerminalsML (G rs s))`


val terminalsML = Define `(terminalsML (G [] s) = LIST_TO_SET []) /\
(terminalsML (G (rule l r::rs) s) = LIST_TO_SET (FILTER isTmnlSym r) UNION terminalsML (G rs s))`



val nonTerminalsEq = store_thm ("nonTerminalsEq",
``nonTerminals g = nonTerminalsML g``,
Cases_on `g` THEN
Induct_on `l` THEN
SRW_TAC [] [nonTerminals, nonTerminalsML] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,nonTerminalsML,isNonTmnlSym_def,nonTerminals] THEN
`nonTerminalsML (G l s) = NTS s INSERT BIGUNION (IMAGE rule_nonterminals (set l))` by SRW_TAC [] [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
Q.ABBREV_TAC `a = BIGUNION (IMAGE rule_nonterminals (set l))` THEN
SRW_TAC [] [filter_seteq,insert_union,isNonTmnlSym_def]
)


val terminalsEq = store_thm ("terminalsEq",
``terminals g = terminalsML g``,
Cases_on `g` THEN
Induct_on `l` THEN
SRW_TAC [] [terminals, terminalsML] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [terminalsML,isTmnlSym_def,terminals, rule_terminals] THEN
`terminalsML (G l s) = BIGUNION (IMAGE rule_terminals (set l))` by SRW_TAC [] [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
Q.ABBREV_TAC `a = BIGUNION (IMAGE rule_terminals (set l))` THEN
SRW_TAC [] [filter_seteq,insert_union,isTmnlSym_def]
)


val allSyms = Define `allSyms g = nonTerminals g UNION terminals g`


val allSymsML = Define `allSymsML g = nonTerminalsML g UNION terminalsML g`


val allSymsEq = store_thm ("allSymsEq",
``allSyms g = allSymsML g``,
METIS_TAC [allSyms, allSymsML, terminalsEq, nonTerminalsEq,
NOT_EQUAL_SETS])

val derives = Define `
  derives g lsl rsl = ?s1 s2 rhs lhs. (s1 ++ [NTS lhs] ++ s2 = lsl) /\
                                      (s1 ++ rhs ++ s2 = rsl) /\
                                      (MEM (rule lhs rhs) (rules g))`;


val lderives = Define `
  lderives g lsl rsl = ?s1 s2 rhs lhs. (s1 ++ [NTS lhs] ++ s2 = lsl) /\ EVERY isTmnlSym s1 /\
                                      (s1 ++ rhs ++ s2 = rsl) /\
                                      (MEM (rule lhs rhs) (rules g))`;


val rderives = Define `
  rderives g lsl rsl = ?s1 s2 rhs lhs. (s1 ++ [NTS lhs] ++ s2 = lsl) /\ EVERY isTmnlSym s2 /\
                                      (s1 ++ rhs ++ s2 = rsl) /\
                                      (MEM (rule lhs rhs) (rules g))`;


val gaw = Define `gaw g nt = ?w. RTC (derives g) [nt] w /\ EVERY isTmnlSym w`;

(*
a string  (terminal list) is in L(G) iff
1) the string consists solely of terminals
2) the string can be derived from start symbol
*)

val sforms = Define `sforms g = {tsl | (RTC (derives g) [NTS (startSym g)] tsl)}`;


val language = Define `language g = { tsl | RTC (derives g) [NTS (startSym g)] tsl /\ EVERY isTmnlSym tsl }`


val llanguage = Define `llanguage g = { tsl | RTC (lderives g) [NTS (startSym g)] tsl /\ EVERY isTmnlSym tsl }`

val rlanguage = Define `rlanguage g = { tsl | RTC (rderives g) [NTS (startSym g)] tsl /\ EVERY isTmnlSym tsl }`





(* Given a CFG G = (V, T, P, S), with L(G) != {}, we can effectively find an equivalent
CFG G' = (V', T, P', S) such that foreach A in V' there is some w in T* for which A => w *)

val derives_same_append_left = store_thm ("derives_same_append_left",
	``!g u v.derives g u v ==> !x.derives g (x++u) (x++v)``,
	SRW_TAC [] [derives] THEN MAP_EVERY Q.EXISTS_TAC [`x++s1`,`s2`,`rhs`,`lhs`]
	THEN SRW_TAC [] []);

val derives_same_append_right = store_thm ("derives_same_append_right",
	``!g u v.derives g u v ==> !x.derives g (u++x) (v++x)``,
	SRW_TAC [] [derives] THEN MAP_EVERY Q.EXISTS_TAC [`s1`,`s2++x`,`rhs`,`lhs`]
	THEN SRW_TAC [] []);


val rtc_derives_same_append_left = store_thm ("rtc_derives_same_append_left",
	``!u v.RTC (derives g) u v ==> !x. RTC (derives g) (x++u) (x++v)``,
	HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
	METIS_TAC [relationTheory.RTC_RULES,derives_same_append_left]
);

val b1 = store_thm ("b1",
``!rst. ~RTC (derives g) [] (fst::rst)``,
SRW_TAC [] [Once RTC_CASES1, derives]
)

val rtc_derives_same_append_right = store_thm ("rtc_derives_same_append_right",
	``!u v.RTC (derives g) u v ==> !x. RTC (derives g) (u++x) (v++x)``,
	HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
	METIS_TAC [relationTheory.RTC_RULES,derives_same_append_right]
);


val derives_append = store_thm ("derives_append",
  ``RTC (derives g) M N /\ RTC (derives g) P Q ==>
    RTC (derives g) (M ++ P) (N ++ Q)``,
  Q_TAC SUFF_TAC `!x y. RTC (derives g) x y ==>
                        !u v. RTC (derives g) u v ==>
                              RTC (derives g) (x ++ u) (y ++ v)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THENL [
    		METIS_TAC [rtc_derives_same_append_left],
		METIS_TAC [derives_same_append_right,RTC_RULES]]);


val res1 = store_thm ("res1",
	``!lhs rhs g.MEM (rule lhs rhs) (rules g) ==> derives g [NTS lhs] rhs``,
	SRW_TAC [] [derives] THEN MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`]
	THEN SRW_TAC [] []);



val res2 = store_thm ("res2",
``!g a b.derives g a b ==> !c.derives g b c ==> RTC (derives g) a c``,
SRW_TAC [] [] THEN METIS_TAC [RTC_SUBSET,RTC_RTC]
);


val res3 = store_thm ("res3",
``!g a b.derives g a b ==> !c.RTC (derives g) b c ==> RTC (derives g) a c``,
SRW_TAC [] [] THEN METIS_TAC [RTC_SUBSET,RTC_RTC]);


val slres = store_thm ("slres",
``(s1 ++ [NTS lhs] ++ s2 = [NTS s]) ==> (lhs=s)``,
Cases_on `s1` THEN SRW_TAC [] []);

val slres2 = store_thm ("slres2",
``(s1 ++ [NTS lhs] ++ s2 = [NTS s]) ==> (s1=[]) /\ (s2=[])``,
Cases_on `s1` THEN SRW_TAC [] []);


val rgr_r8 = store_thm ("rgr_r8",
``(r=r1++[sym]++r2) ==> derives g [NTS l] r ==>  (?a b.derives g [NTS l] (a++[sym]++b))``,
METIS_TAC []
);


(*
Useless symbols
A symbol X is useful if there is a derivation S *=> aXb *=> w for some a,b,w where w in T*.
but have to handle the case where X may only occur in sentential forms containing a useless
symbol itself.
*)

(*
Lemma 4.2
Given a CFG G = (V T P S) we can effectively find an
equivalent CFG G' = (V', T', P', S) such that for each X in V'UT'
there exists a and b in (V'UT')* for which S=>*aXb.
*)


val is_null = Define `is_null g r = !w.RTC (derives g) r w ==> is_word w ==> (w=[]) `;

(*
Theorem 4.3

If L=L(G) for some CFG G = (V,T,P,S), then L-{e} is L(G') for a CFG G' with no useless symbols or e-productions.
*)

(*
 Lemma 4.3
Define an A-production to be a production with variable A on the
left. Let G=(V,T,P,S) be a CFG. Let A->xBy be a production in P and
B->b1|b2... be the set of all B-productions. Let G1=(V,T,P1,S) be
obtained from G by deleting the production A->xBy from P and adding
the productions A->xb1y|xb2y.... Then L(g)=L(G1).
*)





(*
Theorem 4.6
Every CFL L without e can be generated by a grammar for
which every production is of the form A->aalph, where A is a variable,
a is a terminal and alpha (possibly empty) is a string of variables.
*)

val numTmnls = Define `(numTmnls [] = 0)
/\ (numTmnls (r::rs) = if isTmnlSym r then 1+numTmnls rs else numTmnls rs)`


val sub_result = store_thm ("sub_result",
  ``!g symlist.EVERY (gaw g) symlist ==>
    ?w. RTC (derives g) symlist w /\ EVERY isTmnlSym w``,
STRIP_TAC THEN
  Induct_on `symlist` THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `[]` THEN SRW_TAC [][RTC_RULES],
    FULL_SIMP_TAC (srw_ss()) [gaw] THEN
    Q.EXISTS_TAC `w' ++ w` THEN SRW_TAC [] [] THEN
    `RTC (derives g) (h::symlist) (w' ++ w) = RTC (derives g) ([h]++symlist) (w' ++ w)` by SRW_TAC [] [] THEN
    ASM_REWRITE_TAC [] THEN METIS_TAC [derives_append]]);


val key_result = store_thm ("key_result",
  ``EVERY (gaw g) v /\ derives g u v ==> EVERY (gaw g) u``,
  SRW_TAC [][derives] THEN
  FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND] THEN `EVERY (gaw g) rhs ==>
    ?w. RTC (derives g) rhs w /\ EVERY isTmnlSym w` by FULL_SIMP_TAC (srw_ss()) [gaw,sub_result]
THEN RES_TAC THEN SRW_TAC [] [gaw] THEN
`!lhs rhs g.MEM (rule lhs rhs) (rules g) ==> derives g [NTS lhs] rhs` by FULL_SIMP_TAC (srw_ss()) [res1]
THEN RES_TAC THEN METIS_TAC [RTC_RULES]);

val sub_result_rev = store_thm ("sub_result_rev",
``!symlist.(?w. RTC (derives g) symlist w /\ EVERY isTmnlSym w) ==> EVERY (gaw g) symlist``,
Q_TAC SUFF_TAC `!symlist w.RTC (derives g) symlist w ==> EVERY isTmnlSym w ==> EVERY (gaw g) symlist`
THEN1 METIS_TAC [] THEN HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] []
THENL [Induct_on `symlist` THEN SRW_TAC [] [gaw] THEN Q.EXISTS_TAC `[h]` THEN SRW_TAC [] [RTC_RULES],
METIS_TAC [key_result]]);

val term_syms_gen_words = store_thm ("term_syms_gen_words",
  ``EVERY isTmnlSym w ==> EVERY (gaw g) w``,
  METIS_TAC [RTC_RULES, sub_result_rev])



val upgr_r7 = store_thm("upgr_r7",
``! u z.RTC (derives g) u z ==> (u=x++y) ==> ?x' y'. (z=x'++y') ==> RTC (derives g) x x' /\ RTC (derives g) y y'``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
  MAP_EVERY Q.EXISTS_TAC [`x`,`y`] THEN SRW_TAC [] [RTC_RULES,RTC_REFLEXIVE],
  FULL_SIMP_TAC (srw_ss()) [derives] THEN METIS_TAC []
]);


val lupgr_r7 = store_thm("lupgr_r7",
``! u z.RTC (lderives g) u z ==> (u=x++y) ==> ?x' y'. (z=x'++y') ==> RTC (lderives g) x x' /\ RTC (lderives g) y y'``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
  MAP_EVERY Q.EXISTS_TAC [`x`,`y`] THEN SRW_TAC [] [RTC_RULES,RTC_REFLEXIVE],
  FULL_SIMP_TAC (srw_ss()) [lderives] THEN METIS_TAC []
]);

val upgr_r11 = store_thm("upgr_r11",
``derives g [NTS lhs] [NTS rhs] ==> MEM (rule lhs [NTS rhs]) (rules g)``,
SRW_TAC [] [derives,lreseq]
);

val lupgr_r11 = store_thm("lupgr_r11",
``lderives g [NTS lhs] [NTS rhs] ==> MEM (rule lhs [NTS rhs]) (rules g)``,
SRW_TAC [] [lderives,lreseq]
);


val upgr_r15 = store_thm("upgr_r15",
``!u v.RTC (derives g) u v ==> (u=s1++lhs'++s2) ==> MEM (rule lhs lhs') (rules g) ==> RTC (derives g) (s1++[NTS lhs]++s2) v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THENL[
METIS_TAC [res1,rtc_derives_same_append_right,rtc_derives_same_append_left,RTC_SUBSET],
METIS_TAC [RTC_RULES_RIGHT1]
]);



val rtc_r1 = store_thm("rtc_r1",
``RTC (derives g) s1 s2 ==> ~(s1=s2) ==> (?sf.derives g s1 sf /\ RTC (derives g) sf s2)``,
REWRITE_TAC [Once RTC_CASES1] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]
);

val upgr_r18 = store_thm("upgr_r18",
``derives g s s' ==> (?pfx sfx.(s'=pfx++sfx) /\ derives g s pfx)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives] THEN
MAP_EVERY Q.EXISTS_TAC [`s1++rhs++s2`,`[]`] THEN
SRW_TAC [] [] THEN
METIS_TAC []
);


val lemma2 = store_thm("lemma2",
``!s1 s2 s1' s2'.derives g (s1++s2) s ==> (?s1'.derives g s1 s1' /\ (s=s1'++s2)) \/ (?s2'.derives g s2 s2' /\ (s=s1++s2'))``,
SRW_TAC [] [] THEN
RULE_ASSUM_TAC (REWRITE_RULE [derives]) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`?l1 l2.((s1=s1'++[NTS lhs]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/ ((s2=l2++[NTS lhs]++s2') /\ (s1=l1) /\ (s1'=l1++l2))` by METIS_TAC [list_r6] THENL[
DISJ1_TAC THEN SRW_TAC [] [derives] THEN METIS_TAC [],
DISJ2_TAC THEN SRW_TAC [] [derives] THEN METIS_TAC [APPEND_ASSOC]])

val llemma2 = store_thm("llemma2",
``!s1 s2 s1' s2'.lderives g (s1++s2) s ==> (?s1'.lderives g s1 s1' /\ (s=s1'++s2)) \/ (?s2'.lderives g s2 s2' /\ (s=s1++s2'))``,
SRW_TAC [] [] THEN
RULE_ASSUM_TAC (REWRITE_RULE [lderives]) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`?l1 l2.((s1=s1'++[NTS lhs]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/ ((s2=l2++[NTS lhs]++s2') /\ (s1=l1) /\ (s1'=l1++l2))`
by METIS_TAC [list_r6] THENL[
DISJ1_TAC THEN SRW_TAC [] [lderives] THEN METIS_TAC [],
DISJ2_TAC THEN SRW_TAC [] [lderives] THEN
Q.EXISTS_TAC `l2++rhs++s2'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
MAP_EVERY Q.EXISTS_TAC [`l2`,`s2'`,`rhs`,`lhs`] THEN
METIS_TAC [APPEND_ASSOC]])


val upgr_r17 = store_thm("upgr_r17",
``! u v.RTC (derives g) u v ==> (u=x++y) ==> (?x' y'. ((v=x'++y') /\ RTC (derives g) x x' /\ RTC (derives g) y y' ))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(?x''.derives g x' x'' /\ (v'=x''++y')) \/ (?y''.derives g y' y'' /\ (v'=x'++y''))` by METIS_TAC [lemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]
])


val lupgr_r17 = store_thm("lupgr_r17",
``! u v.RTC (lderives g) u v ==> (u=x++y) ==> (?x' y'. ((v=x'++y') /\ RTC (lderives g) x x' /\ RTC (lderives g) y y' ))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(?x''.lderives g x' x'' /\ (v'=x''++y')) \/ (?y''.lderives g y' y'' /\ (v'=x'++y''))` by METIS_TAC [llemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]])


val upgr_r19 = store_thm("upgr_r19",
``! u v.RTC (derives g) u v ==> (u=x++y++z) ==> (?x' y' z'. ((v=x'++y'++z') /\ RTC (derives g) x x' /\ RTC (derives g) y y' /\ RTC (derives g) z z'))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THEN
` derives g (x' ++ (y' ++ z')) v' ==> (?x''.derives g x' x'' /\ (v'=x''++(y'++z'))) \/ (?y''.derives g (y'++z') y'' /\ (v'=x'++y''))` by SRW_TAC [][lemma2,APPEND,APPEND_ASSOC] THEN
  ` derives g (x' ++ y' ++ z') v' =  derives g (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] THEN
  RES_TAC THENL[
  METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],

  RES_TAC THEN
`derives g (y' ++ z') y'' ==> (?s1'.derives g y' s1' /\ (y''=s1'++z')) \/ (?s2'.derives g z' s2' /\ (y''=y'++s2'))` by METIS_TAC [lemma2] THEN
   RES_TAC THEN
   METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]])


val lupgr_r19 = store_thm("lupgr_r19",
``! u v.RTC (lderives g) u v ==> (u=x++y++z) ==> (?x' y' z'. ((v=x'++y'++z') /\ RTC (lderives g) x x' /\ RTC (lderives g) y y' /\
RTC (lderives g) z z'))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THEN
` lderives g (x' ++ (y' ++ z')) v' ==> (?x''.lderives g x' x'' /\ (v'=x''++(y'++z'))) \/ (?y''.lderives g (y'++z') y'' /\ (v'=x'++y''))`
by SRW_TAC [][llemma2,APPEND,APPEND_ASSOC] THEN
  ` lderives g (x' ++ y' ++ z') v' =  lderives g (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] THEN
  RES_TAC THENL[
  METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],
  RES_TAC THEN
`lderives g (y' ++ z') y'' ==> (?s1'.lderives g y' s1' /\ (y''=s1'++z')) \/ (?s2'.lderives g z' s2' /\ (y''=y'++s2'))`
by METIS_TAC [llemma2] THEN SRW_TAC [] [] THEN
   RES_TAC THEN
   METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]])

val slemma1_4 = store_thm("slemma1_4",
``(NTS nt IN nonTerminals g) = (?rhs.MEM (rule nt rhs) (rules g) \/ ?l p s.MEM (rule l (p++[NTS nt]++s))(rules g) \/ (nt=startSym g))``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules,startSym] THENL[
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,INSERT_DEF] THEN METIS_TAC [rules,rgr_r9eq],
FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules,startSym] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `rule_nonterminals (rule nt rhs)` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,rules,INSERT_DEF],
METIS_TAC []],
FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules,startSym] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `rule_nonterminals (rule l' (p ++ [NTS nt] ++ s'))` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,rules,INSERT_DEF,isNonTmnlSym_def],
METIS_TAC [rules]]
])

val slemma1_4Tmnls = store_thm("slemma1_4Tmnls",
``(TS t IN terminals g) = ?l p s.MEM (rule l (p++[TS t]++s)) (rules g)``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [terminals,rules,startSym] THENL[
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [rule_terminals,INSERT_DEF] THEN METIS_TAC [rules,rgr_r9eq],
FULL_SIMP_TAC (srw_ss()) [terminals,rules,startSym] THEN
Q.EXISTS_TAC `rule_terminals (rule l' (p ++ [TS t] ++ s'))` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_terminals,rules,INSERT_DEF,isTmnlSym_def],
METIS_TAC [rules]]
])


val slemma1_3 = store_thm("slemma1_3",
``~(NTS nt IN nonTerminals g) = (~(?rhs.MEM (rule nt rhs) (rules g)) /\ ~(?l p s.MEM (rule l (p++[NTS nt]++s)) (rules g)) /\ ~(nt=startSym g))``,
METIS_TAC [slemma1_4,DE_MORGAN_THM]
)

val emptySetList = store_thm ("emptySetList",
``(({} = LIST_TO_SET l) = (l=[]))``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM] THEN METIS_TAC [listNotEmpty,rgr_r9eq])


val finiteNtsList = store_thm("finiteNtsList",
``!s.FINITE s ==> !g.(s=(LIST_TO_SET (rules g))) ==> FINITE (nonTerminals g)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
Cases_on `g`  THEN SRW_TAC [] [nonTerminals] THENL[
FULL_SIMP_TAC (srw_ss()) [rules] THEN METIS_TAC [emptySetList,MEM]],
Cases_on `g`  THEN
SRW_TAC [] [nonTerminals] THEN
Cases_on `x` THEN
`FINITE (LIST_TO_SET l')` by METIS_TAC [finiteLists] THEN
SRW_TAC [] [rule_nonterminals] THEN
`{nt | isNonTmnlSym nt /\ MEM nt l'} = {nt | isNonTmnlSym nt /\ nt IN (LIST_TO_SET l')}` by SRW_TAC [] [SET_TO_LIST_IN_MEM] THEN
ASM_REWRITE_TAC [] THEN
`{nt | isNonTmnlSym nt /\ nt IN (LIST_TO_SET l')} SUBSET (LIST_TO_SET l')` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]  THEN
METIS_TAC [SUBSET_FINITE]]
)

val rt1 = store_thm ("rt1",
``!e r.(e IN rule_terminals r) ==> ~(isNonTmnlSym e)``,
Cases_on `e` THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

SRW_TAC [] [] THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [rule_terminals] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]])



val rt2 = store_thm (
  "rt2",
  ``!e. ~isNonTmnlSym e ==> ?r. e IN rule_terminals r``,
  SRW_TAC [] [] THEN
  Cases_on `e` THENL [
    Q.EXISTS_TAC `rule l [TS s]` THEN
    SRW_TAC [] [rule_terminals] THEN
    METIS_TAC [isTmnlSym_def,isNonTmnlSym_def],
    METIS_TAC [isNonTmnlSym_def]
  ])


val rt = store_thm ("rt",
``!e.(?r.e IN rule_terminals r) = ~(isNonTmnlSym e)``,
METIS_TAC [rt1,rt2,EQ_IMP_THM])


val ntsNotInTmnls1 = store_thm ("ntsNotInTmnls1",
``!nt.isNonTmnlSym nt ==> ~(nt IN terminals g)``,
Cases_on `nt` THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],
Cases_on `g` THEN
SRW_TAC [] [terminals] THEN
METIS_TAC [isNonTmnlSym_def,rt]])


val ntsNotInTmnls = store_thm ("ntsNotInTmnls",
``!nt.~((NTS nt) IN (terminals g))``,
Cases_on `g` THEN
SRW_TAC [] [terminals] THEN METIS_TAC [isNonTmnlSym_def,rt])


val rnt1 = store_thm ("rnt1",
``!e r.(e IN rule_nonterminals r) ==> ~(isTmnlSym e)``,
Cases_on `e` THENL[
SRW_TAC [] [] THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]])



val rnt2 = store_thm (
  "rnt2",
  ``!e. ~(isTmnlSym e) ==> ?r.(e IN rule_nonterminals r)``,
  Cases_on `e` THEN SRW_TAC [][isTmnlSym_def, isNonTmnlSym_def] THEN
  Q.EXISTS_TAC `rule l [NTS s]` THEN
  SRW_TAC [] [rule_nonterminals, isNonTmnlSym_def]);

val rnt = store_thm ("rnt",
``!e.(?r.e IN rule_nonterminals r) = ~(isTmnlSym e)``,
METIS_TAC [rnt1,rnt2,EQ_IMP_THM])

val tsNotInNonTmnls = store_thm ("tsNotInNonTmnls",
``!ts.~((TS ts) IN (nonTerminals g))``,
Cases_on `g` THEN
SRW_TAC [] [nonTerminals] THEN
METIS_TAC [rnt,isTmnlSym_def])


val allNtSymsInGr = store_thm("allNtSymsInGr",
``!nt.((NTS nt) IN allSyms g) = (?rhs.MEM (rule nt rhs) (rules g)) \/ (?l p s.MEM (rule l (p++[NTS nt]++s))(rules g))
\/ ((nt=startSym g))``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [allSyms] THEN
METIS_TAC [slemma1_4,ntsNotInTmnls])

val allTmSymsInGr = store_thm("allTmSymsInGr",
``!ts.((TS ts) IN allSyms g) = ?l p s.MEM (rule l (p++[TS ts]++s))(rules g)``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [allSyms] THENL[
METIS_TAC [tsNotInNonTmnls],

FULL_SIMP_TAC (srw_ss()) [terminals] THEN
Cases_on `x` THEN
FULL_SIMP_TAC (srw_ss()) [rule_terminals,rules,rgr_r9eq] THEN
METIS_TAC [],

SRW_TAC [] [allSyms] THEN
DISJ2_TAC THEN
SRW_TAC [] [terminals] THEN
FULL_SIMP_TAC (srw_ss()) [rules] THEN
Q.EXISTS_TAC `rule_terminals (rule l' (p++[TS ts]++s'))` THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [rule_terminals] THEN
METIS_TAC [isTmnlSym_def],
METIS_TAC []]])

val symInGr = store_thm ("symInGr",
``!sym g.~(lhsWithLastSym sym (rules g)=[]) ==> sym IN (allSyms g)``,
SRW_TAC [] [] THEN
`(?l pfx.MEM (rule l (pfx++[sym])) (rules g))` by METIS_TAC [notNullLhsLastSym] THEN
Cases_on `sym` THEN
METIS_TAC [allNtSymsInGr,allTmSymsInGr,notNullLhsLastSym,APPEND_NIL])


val finiteTerminals = store_thm("finiteTerminals",
``!s.FINITE s ==> !g.(s=(LIST_TO_SET(rules g))) ==> FINITE (terminals g)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
Cases_on `g`  THEN SRW_TAC [] [terminals] THENL[
FULL_SIMP_TAC (srw_ss()) [rules] THEN METIS_TAC [emptySetList,MEM]],
Cases_on `g`  THEN
SRW_TAC [] [terminals] THEN
Cases_on `x` THEN
`FINITE (LIST_TO_SET l')` by METIS_TAC [finiteLists] THEN
SRW_TAC [] [rule_terminals] THEN
`{tmnl | isTmnlSym tmnl /\ MEM tmnl l'} = {tmnl | isTmnlSym tmnl /\ tmnl IN (LIST_TO_SET l')}` by SRW_TAC [] [SET_TO_LIST_IN_MEM] THEN
ASM_REWRITE_TAC [] THEN
`{tmnl | isTmnlSym tmnl /\ tmnl IN (LIST_TO_SET l')} SUBSET (LIST_TO_SET l')` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]  THEN
METIS_TAC [SUBSET_FINITE]])

val finiteAllSyms = store_thm ("finiteAllSyms",
``!s.FINITE s ==> !g.(s=(LIST_TO_SET(rules g))) ==> FINITE (allSyms g)``,
SRW_TAC [] [allSyms] THEN
METIS_TAC [finiteNtsList,finiteTerminals])

val nullable = Define `nullable g sl = RTC (derives g) sl []`;

val getRhs = Define `(getRhs l [] = []) /\
(getRhs l ((rule l' r)::rs) = if (l=l') then ([r]++getRhs l rs) else getRhs l rs)`

val derivesNull = Define `(derivesNull g (TS ts) = T) /\
(derivesNull g (NTS nt) = MEM (rule nt []) (rules g))`;

val numNonTmnls = Define `(numNonTmnls [] = 0) /\
(numNonTmnls (rule l r::rs) = 1 + LENGTH (FILTER isNonTmnlSym r) + numNonTmnls rs)`

val getRhsDistrib = store_thm ("getRhsDistrib",
``!l1 l2.getRhs A (l1++l2) = getRhs A l1 ++ getRhs A l2``,
Induct_on `l1` THEN
SRW_TAC [] [getRhs] THEN
Cases_on `h` THEN
SRW_TAC [] [getRhs]
)

val x_1 = store_thm ("x_1",
``MEM e (getRhs A (rules g)) = derives g [NTS A] e``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [derives,rules] THEN
Induct_on `l` THENL[
SRW_TAC [] [getRhs],
SRW_TAC [] [] THEN
Cases_on `h` THEN
Cases_on `A=s` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs] THENL[
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`l'`,`A`] THEN
SRW_TAC [] [],

METIS_TAC [],
METIS_TAC [getRhs]]],

FULL_SIMP_TAC (srw_ss()) [derives] THEN
`(s1=[])/\ (s2=[]) /\ ([NTS A]=[NTS lhs])` by METIS_TAC [lreseq] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
`getRhs A (r1++[rule A rhs]++r2) = getRhs A r1 ++ getRhs A [rule A rhs] ++ getRhs A r2` by METIS_TAC [getRhsDistrib,APPEND_ASSOC] THEN
ASM_REWRITE_TAC [] THEN
SRW_TAC [] [getRhs] THEN
METIS_TAC []])

val notNullGetRhs_1 = store_thm ("notNullGetRhs_1",
``!nt g.~(getRhs nt (rules g)=[]) ==> (?r.MEM (rule nt r) (rules g))``,
SRW_TAC [] [] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules] THEN
Induct_on `l` THENL[
SRW_TAC [] [] THEN METIS_TAC [getRhs],
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs] THEN
METIS_TAC [getRhs]])

val notNullGetRhs_2 = store_thm ("notNullGetRhs_2",
``(?r.MEM (rule nt r) (rules g)) ==> ~(getRhs nt (rules g)=[])``,
SRW_TAC [] [] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules] THEN
Induct_on `l` THENL[
SRW_TAC [] [] THEN METIS_TAC [getRhs],
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs] THEN
SRW_TAC [] []])

val notNullGetRhs = store_thm ("notNullGetRhs",
``(?r.MEM (rule nt r) (rules g)) = ~(getRhs nt (rules g)=[])``,
METIS_TAC [notNullGetRhs_1,notNullGetRhs_2])


val ntsInGr = store_thm ("ntsInGr",
``!nt g.~(getRhs nt (rules g)=[]) ==> (NTS nt) IN (nonTerminals g)``,
METIS_TAC [slemma1_4,notNullGetRhs])

val nullableList = Hol_defn "nullableList" `(nullableML g sn [] = T) /\
(nullableML g sn [TS ts] = F) /\
(nullableML g sn [NTS A] = if (MEM (NTS A) sn) then F
		else EXISTS (nullableML g (NTS A :: sn))
                            (getRhs A (rules g))) /\
(nullableML g sn (s::ss) = nullableML g sn [s] /\ nullableML g sn ss)`


val (nullableML,nullable_ind) = tprove(nullableList,
WF_REL_TAC (`inv_image ((measure (\(g,sn). CARD ((nonTerminals g) DIFF (LIST_TO_SET sn)))) LEX (measure (\(syms).LENGTH syms))) (\(g,sn,syms).((g,sn),syms))`) THEN
SRW_TAC [] [] THENL[
`FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
`FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`FINITE (NTS A INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
FULL_SIMP_TAC (srw_ss()) [CARD_DIFF] THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [CARD_INSERT,FINITE_LIST_TO_SET] THEN
`~(getRhs A (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
`(NTS A) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
`(nonTerminals g INTER (NTS A INSERT set sn)) = (NTS A INSERT set sn) INTER nonTerminals g` by METIS_TAC [INTER_COMM] THEN
ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
SRW_TAC [] [ADD1] THEN
`(nonTerminals g INTER set sn) = (set sn INTER nonTerminals g)` by METIS_TAC [INTER_COMM] THEN
ASM_REWRITE_TAC [] THEN
DECIDE_TAC,

`~(getRhs A (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
`(NTS A) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
`~((NTS A) IN set sn)` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
`~(NTS A IN (nonTerminals g INTER set sn))` by METIS_TAC [IN_INTER] THEN
`~(nonTerminals g = set sn)` by METIS_TAC [] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
`FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`FINITE (NTS A INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
`CARD (nonTerminals g) - CARD (nonTerminals g INTER set sn) = CARD ((nonTerminals g) DIFF (set sn))` by METIS_TAC [CARD_DIFF] THEN
ASM_REWRITE_TAC [] THEN
`(NTS A) IN (nonTerminals g DIFF set sn)` by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
`~((nonTerminals g DIFF set sn)={})` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
`~(CARD (nonTerminals g DIFF set sn)=0)` by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
DECIDE_TAC ],

DECIDE_TAC,
DECIDE_TAC])

val _ = save_thm ("nullableML",nullableML)
val _ = save_thm ("nullableML_ind",nullable_ind)


val lhsWithNullSfx = Define `(lhsWithNullSfx g [] = []) /\
(lhsWithNullSfx g ((l,sfx)::rst) = if (nullable g sfx) then ([NTS l]::lhsWithNullSfx g rst) else lhsWithNullSfx g rst)`

val sfxNotNull = Define `(sfxNotNull g [] = []) /\
(sfxNotNull g ((l,sfx)::rst) = if ~(nullable g sfx) then (sfx::sfxNotNull g rst) else sfxNotNull g rst)`

val notTmnlDerives = store_thm("notTmnlDerives",
``!l.~(derives g [TS s] l)``,
SRW_TAC [] [derives] THEN
DISJ1_TAC THEN
`~(MEM (NTS lhs) [TS s])` by SRW_TAC [] [] THEN
METIS_TAC [rgr_r9eq])

val notTlDerives = store_thm("notTlDerives",
``!l.~(derives g (TS s::rst) [])``,
SRW_TAC [] [derives])

val notTmnlRtcDerives1 = store_thm ("notTmnlRtcDerives1",
``!ts l.RTC (derives g) [TS ts] l ==> (l=[TS ts])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
METIS_TAC [notTmnlDerives])

val notTmnlRtcDerives2 = store_thm ("notTmnlRtcDerives2",
``!tl l.(l=[TS ts]) ==> RTC (derives g) [TS ts] l``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1])

val notTmnlRtcDerives = store_thm ("notTmnlRtcDerives",
``!tl l.RTC (derives g) [TS ts] l = (l=[TS ts])``,
METIS_TAC [notTmnlRtcDerives1,notTmnlRtcDerives2])

val n0_1 = store_thm ("n0_1",
``!l1 l2.derives g l1 l2 ==> (MEM (TS ts) l1) ==> (MEM (TS ts) l2)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives,rgr_r9eq] THEN
`s1++[NTS lhs]++s2 = r1'++([TS ts] ++ r2')` by SRW_TAC [] [] THEN
`?l1 l2. (r1' = s1 ++ [NTS lhs] ++ l1) /\ ([TS ts]++r2' = l2) /\ (s2 = l1 ++ l2) \/
(([TS ts] ++ r2') = l2 ++ [NTS lhs] ++ s2) /\ (r1' = l1) /\ (s1 = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [] [] THENL[
METIS_TAC [APPEND_ASSOC],
`?l1 l2.([TS ts] = l2' ++ [NTS lhs] ++ l1) /\ (r2' = l2) /\ (s2 = l1 ++ l2) \/
(r2' = l2 ++ [NTS lhs] ++ s2) /\ ([TS ts] = l1) /\ (l2' = l1 ++ l2)` by METIS_TAC [list_r6] THENL[
`(l2'=[]) /\ (l1=[]) /\ ([TS ts] = [NTS lhs])` by METIS_TAC [lreseq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
METIS_TAC [APPEND_ASSOC]]]
)

val mem_r1 = store_thm ("mem_r1",
``!l.~(l=[]) = ?e.MEM e l``,
SRW_TAC [] [EQ_IMP_THM] THEN
Induct_on `l` THEN
SRW_TAC [] [] THEN
METIS_TAC [])




val notTlRtcDerives_r1 = store_thm ("notTlRtcDerives_r1",
``!x y.RTC (derives g) x y ==> (?ts.MEM (TS ts) x) ==> ~(y=[])``,
HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [] [] THENL[
ONCE_REWRITE_TAC [mem_r1] THEN METIS_TAC [],

RES_TAC THEN
METIS_TAC [n0_1]])



val notTlRtcDerives = store_thm ("notTlRtcDerives",
``!tl l.~(RTC (derives g) (TS ts::rst) [])``,
SRW_TAC [] [] THEN
METIS_TAC [notTlRtcDerives_r1,MEM])

val n4_1 = store_thm ("n4_1",
``!s1 s2.nullableML g sn (s1++s2) ==> (nullableML g sn s1 /\ nullableML g sn s2)``,
SRW_TAC [] [] THEN
Induct_on `s1` THEN
SRW_TAC [] [nullableML] THENL[
Induct_on `s1` THEN
SRW_TAC [] [] THENL[
Induct_on `s2` THEN
SRW_TAC [] [] THEN
Cases_on `h` THEN METIS_TAC [nullableML],

SRW_TAC [] [] THEN
Cases_on `h` THEN METIS_TAC [nullableML]],

Induct_on `s1` THEN
Induct_on `s2` THEN
SRW_TAC [] [] THENL[
METIS_TAC [nullableML],
Cases_on `h` THEN Cases_on `h'` THEN METIS_TAC [nullableML],
Cases_on `h` THEN Cases_on `h'` THEN METIS_TAC [nullableML],
Cases_on `h` THEN Cases_on `h'` THEN METIS_TAC [nullableML]]]
)

val n4_2 = store_thm ("n4_2",
``!s1 s2. (nullableML g sn s1 /\ nullableML g sn s2) ==> nullableML g sn (s1++s2)``,
SRW_TAC [] [] THEN
Induct_on `s1` THEN
SRW_TAC [] [nullableML] THENL[
Induct_on `s1` THEN
SRW_TAC [] [] THENL[
Induct_on `s2` THEN
SRW_TAC [] [] THEN
Cases_on `h` THEN METIS_TAC [nullableML],

SRW_TAC [] [] THEN
Cases_on `h` THEN METIS_TAC [nullableML]]])

val n4 = store_thm ("n4",
``!s1 s2.  nullableML g sn (s1++s2)= (nullableML g sn s1 /\ nullableML g sn s2)``,
METIS_TAC [n4_1,n4_2])

val n5 = store_thm ("n5",
``RTC (derives g) [TS ts] [] = nullableML g sn [TS ts]``,
SRW_TAC [] [EQ_IMP_THM] THEN
METIS_TAC [nullableML,notTmnlRtcDerives]);

val R = ``inv_image ((measure (\(g,sn). CARD ((nonTerminals g) DIFF (LIST_TO_SET sn)))) LEX (measure (\syms : symbol list. LENGTH syms))) (\(g,sn,syms).((g,sn),syms))``

val R_IND = (Q.GEN `P` o
             SIMP_RULE (srw_ss()) [relationTheory.inv_image_def,
                                   pairTheory.LEX_DEF, FORALL_AND_THM,
                                   DISJ_IMP_THM,
                                   prim_recTheory.measure_def] o
             Q.SPEC `\(g, sn, x). P g sn x` o
             SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD] o
             SIMP_RULE (srw_ss()) [relationTheory.WF_inv_image,
                                  pairTheory.WF_LEX,
                                  prim_recTheory.WF_measure])
                (ISPEC R relationTheory.WF_INDUCTION_THM)

val nullableML' = prove(
  ``(nullableML g sn [] = T) /\
    (nullableML g sn (TS x :: t) = F) /\
    (nullableML g sn (NTS n :: t) =
       if MEM (NTS n) sn then F
       else
         EXISTS (nullableML g (NTS n :: sn)) (getRhs n (rules g)) /\
         nullableML g sn t)``,
  SRW_TAC [][nullableML] THEN
  Cases_on `t` THEN SRW_TAC [boolSimps.ETA_ss][nullableML, CONJ_ASSOC]);

open rich_listTheory
val mnlist_lemma = prove(
  ``!x e y a b. (x ++ [e] ++ y = a ++ b) ==>
                IS_PREFIX x a \/ IS_PREFIX a (x ++ [e])``,
  Induct THEN Cases_on `a` THEN SRW_TAC [][IS_PREFIX] THEN METIS_TAC []);

val derives_split_append0 = prove(
  ``!x y. RTC (derives g) x y ==>
          !x0 x1. (x = x0 ++ x1) ==>
                  ?y0 y1. (y = y0 ++ y1) /\ RTC (derives g) x0 y0 /\
                          RTC (derives g) x1 y1``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THENL [
    METIS_TAC [RTC_RULES],
    FULL_SIMP_TAC (srw_ss()) [derives] THEN
    `IS_PREFIX s1 x0 \/ IS_PREFIX x0 (s1 ++ [NTS lhs])`
        by METIS_TAC [mnlist_lemma]
    THENL [
      `?x0'. s1 = x0 ++ x0'` by METIS_TAC [IS_PREFIX_APPEND] THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`x0`, `x0' ++ rhs ++ s2`] MP_TAC) THEN
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`y0`, `y1`] THEN
      `x1 = x0' ++ [NTS lhs] ++ s2`
          by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
      SRW_TAC [][] THEN
      METIS_TAC [derives, RTC_RULES],
      `?s1'. s1 ++ [NTS lhs] ++ s1' = x0` by METIS_TAC [IS_PREFIX_APPEND] THEN
      SRW_TAC [][] THEN
      `s2 = s1' ++ x1` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`s1 ++ rhs ++ s1'`, `x1`] MP_TAC) THEN
      SRW_TAC [][] THEN
      METIS_TAC [derives, RTC_RULES]
    ]
  ]);
val derives_split_append = SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] derives_split_append0


val nullable_APPEND = store_thm(
  "nullable_APPEND",
  ``nullable g (x ++ y) = nullable g x /\ nullable g y``,
  SRW_TAC [][nullable, EQ_IMP_THM] THENL [
    IMP_RES_TAC derives_split_append THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
    IMP_RES_TAC derives_split_append THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
    METIS_TAC [derives_append, APPEND]
  ]);

val finite_nts = prove(
  ``FINITE (nonTerminals g)``,
  Cases_on `g` THEN SRW_TAC [][nonTerminals] THEN
  Cases_on `x` THEN SRW_TAC [][rule_nonterminals] THEN
  POP_ASSUM (K ALL_TAC) THEN Induct_on `l'` THEN SRW_TAC [][] THEN
  SRW_TAC [boolSimps.DNF_ss][GSPEC_OR] THEN
  SRW_TAC [][GSPEC_AND] THEN
  METIS_TAC [FINITE_INSERT, FINITE_EMPTY, INTER_FINITE, INTER_COMM]);

val nullableEq1 = store_thm ("nullableEq1",
  ``!g sn l. nullableML g sn l ==> nullable g l``,
  HO_MATCH_MP_TAC R_IND THEN
  Cases_on `l` THEN SRW_TAC [][nullableML'] THEN1
    SRW_TAC [][nullable, RTC_RULES] THEN
  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [nullableML'] THEN
  `nullable g t` by METIS_TAC [DECIDE ``x < SUC x``] THEN
  Q_TAC SUFF_TAC `nullable g [NTS s]` THEN1
        METIS_TAC [APPEND, nullable_APPEND] THEN
  `?e. MEM e (getRhs s (rules g)) /\ nullableML g (NTS s::sn) e`
     by METIS_TAC [EXISTS_MEM] THEN
  Q_TAC SUFF_TAC `nullable g e` THEN1
     METIS_TAC [x_1, nullable, RTC_RULES] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`g`, `NTS s :: sn`, `e`] MP_TAC) THEN
  SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  `FINITE (nonTerminals g)` by METIS_TAC [finite_nts] THEN
  SRW_TAC [][] THENL [
    `NTS s IN nonTerminals g` by METIS_TAC [ntsInGr, mem_r1] THEN
    `nonTerminals g INTER (NTS s INSERT set sn) =
       NTS s INSERT (nonTerminals g INTER set sn)`
      by METIS_TAC [INTER_COMM, INSERT_INTER] THEN
    SRW_TAC [][] THEN DECIDE_TAC,
    Q_TAC SUFF_TAC `nonTerminals g INTER set sn PSUBSET nonTerminals g`
          THEN1 METIS_TAC [CARD_PSUBSET, DECIDE ``x < y = 0 < y - x``] THEN
    SRW_TAC [][PSUBSET_DEF, EXTENSION] THEN
    METIS_TAC [ntsInGr, mem_r1]
  ]);


val n6 = store_thm ("n6",
``!h tl.nullableML g [] (h::tl) = nullableML g [] [h] /\ nullableML g [] tl ``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `tl` THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [nullableML])

val n3 = store_thm ("n3",
``!s1 s2.nullableML g [] s1 ==> nullableML g [] s2 ==> nullableML g [] (s1++s2)``,
SRW_TAC [] [] THEN
Induct_on `s1` THEN
SRW_TAC [] [] THEN
`nullableML g [] [h] /\ nullableML g [] s1` by METIS_TAC [n4_1,APPEND] THEN
RES_TAC THEN
METIS_TAC [n6])



val lderivesImpDerives = store_thm ("lderivesImpDerives",
``!x y.RTC (lderives g) x y ==> EVERY isTmnlSym y ==> RTC (derives g) x y``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [lderives] THEN
METIS_TAC [derives, RTC_RULES])

val rderivesImpDerives = store_thm ("rderivesImpDerives",
``!x y.RTC (rderives g) x y ==> EVERY isTmnlSym y ==> RTC (derives g) x y``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives] THEN
METIS_TAC [derives, RTC_RULES])


val drd = store_thm ("drd",
``!l0 l1 l2.derives g l0 l1 ==> rderives g l1 l2 ==> ?l'.rderives g l0 l' /\ derives g l' l2 ``,
SRW_TAC [] [derives, rderives] THEN
Q.ABBREV_TAC `l0=s1++[NTS lhs]++s2` THEN
Q.ABBREV_TAC `l1=s1++rhs++s2` THEN
Cases_on `EVERY isTmnlSym s2` THENL[
METIS_TAC [],
`?x n y.(s2=x++[NTS n]++y) /\ EVERY isTmnlSym y` by METIS_TAC [rightnt] THEN
`(s1++rhs++x=s1') /\ (NTS n = NTS lhs') /\ (y=s2')` by
(MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] (GEN_ALL listeq)) THEN
Q.EXISTS_TAC `isTmnlSym` THEN
SRW_TAC [] [isTmnlSym_def, Abbr `l0`, Abbr `l1`] THEN
METIS_TAC [APPEND_ASSOC]) THEN
SRW_TAC [] [Abbr `l0`, Abbr `l1`] THEN
METIS_TAC [APPEND_ASSOC]])



val nrc_drd = store_thm ("nrc_drd",
``!n l0 l1.NRC (derives g) (SUC n) l0 l1 ==> EVERY isTmnlSym l1 ==> ?l'.rderives g l0 l' /\ NRC (derives g) n l' l1``,
Induct_on `n` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [derives, rderives] THEN
METIS_TAC [EVERY_APPEND],
METIS_TAC [NRC, drd]])


val nrc_drdeq = store_thm ("nrc_drdeq",
``!n l0 l1.NRC (derives g) n l0 l1 ==> EVERY isTmnlSym l1 ==> NRC (rderives g) n l0 l1``,
Induct_on `n` THEN SRW_TAC [] [] THEN
`?l'.rderives g l0 l' /\ NRC (derives g) n l' l1` by METIS_TAC [nrc_drd] THEN
`NRC (rderives g) n l' l1` by METIS_TAC [] THEN
METIS_TAC [NRC])


val derivesImpRderives = store_thm ("derivesImpRderives",
``!l0 l1.RTC (derives g) l0 l1 ==> EVERY isTmnlSym l1 ==> RTC (rderives g) l0 l1``,
METIS_TAC [nrc_drdeq, RTC_NRC, NRC_RTC])

val drd_langeq = store_thm ("drd_langeq",
``!g.language g = rlanguage g``,
SRW_TAC [] [EXTENSION, language, rlanguage, EQ_IMP_THM] THEN
METIS_TAC [derivesImpRderives, rderivesImpDerives])


val nullableEq2 = mk_thm ([],
  ``!g sn l.nullable g l ==> (sn=[]) ==> nullableML g sn l``)

val nullableEq = store_thm ("nullableEq",
``!g l.nullable g l = nullableML g [] l``,
METIS_TAC [nullableEq1, nullableEq2]);



(*

val t1 = store_thm ("t1",
``!g sn.MEM (NTS s) sn ==> ~nullableML g sn [NTS s]``,
SRW_TAC [] [nullableML'])

val t2 = mk_thm ([], 
``RTC (derives g) (NTS s::t) [] ==> RTC (derives g) [NTS s] [] /\ RTC (derives g) t []``)

val t3 = mk_thm ([],
``~MEM (NTS s) sn ==> 
    CARD (nonTerminals g DIFF set (NTS s::sn)) <
    CARD (nonTerminals g DIFF set sn)``)

val t4 = mk_thm ([], 
``RTC (derives g) [NTS s] [] ==> ?e. MEM e (getRhs s (rules g)) /\ RTC (derives g) e []``)


val nullableEq2 = store_thm ("nullableEq2",
  ``!g sn l.nullable g l ==> ((nonTerminals g) INTER (LIST_TO_SET sn) = {}) ==> nullableML g sn l``,
  HO_MATCH_MP_TAC R_IND THEN
  Cases_on `l` THEN SRW_TAC [][nullableML'] THEN
    FULL_SIMP_TAC (srw_ss()) [nullable, RTC_RULES] THEN
  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [nullableML'] THEN
  `RTC (derives g) t [] ==> nullableML g sn t` by METIS_TAC [DECIDE ``x < SUC x``] THEN1
METIS_TAC [notTlRtcDerives] THEN

`nullableML g sn t` by METIS_TAC [t2] THEN
`RTC (derives g) [NTS s] []` by METIS_TAC [t2] THEN
Cases_on `~MEM (NTS s) sn` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN
 ` EXISTS (nullableML g (NTS s::sn)) (getRhs s (rules g)) =
    ?e. MEM e (getRhs s (rules g)) /\ nullableML g (NTS s::sn) e`
     by METIS_TAC [EXISTS_MEM] THEN
ONCE_ASM_REWRITE_TAC [] THEN
`?e. MEM e (getRhs s (rules g)) /\ RTC (derives g) e []` by METIS_TAC [t4] THEN
Q.EXISTS_TAC `e` THEN

val t5 = mk_thm ([], ``RTC (derives g) [NTS s] [] ==> (NTS s) IN nonTerminals g``)
`(NTS s) IN nonTerminals g` by METIS_TAC [t5] THEN

val t6 = mk_thm ([], 
``(nonTerminals g INTER set sn = {}) ==> (NTS s) IN nonTerminals g ==> ~MEM (NTS s) sn``)

SRW_TAC [] [] THEN
METIS_TAC [t3, APPEND, APPEND_NIL, t6],


`~nullableML g sn [NTS s]` by METIS_TAC [t1] THEN
METIS_TAC [t1, t2, nullableEq1, nullable, nullableML']
Cases_on `t` THEN SRW_TAC [] []

------------------------------------------------------

val nullableEq2 = store_thm ("nullableEq2",
  ``!g sn l.nullable g l ==> (sn=[]) ==> nullableML g sn l``,
  ``!g sn l.~nullableML g sn l ==> (sn=[]) ==> ~nullable g l``,
  HO_MATCH_MP_TAC R_IND THEN
  Cases_on `l` THEN SRW_TAC [][nullableML'] THEN
    FULL_SIMP_TAC (srw_ss()) [nullable, RTC_RULES] THEN
  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [nullableML'] THEN
  `RTC (derives g) t [] ==> nullableML g [] t` by METIS_TAC [DECIDE ``x < SUC x``] THEN1
METIS_TAC [notTlRtcDerives] THEN

`nullableML g [] t` by METIS_TAC [t2, DECIDE ``x < SUC x``] THEN
`RTC (derives g) [NTS s] []` by METIS_TAC [t2] THEN
Cases_on `~MEM (NTS s) []` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN
 ` EXISTS (nullableML g [NTS s]) (getRhs s (rules g)) =
    ?e. MEM e (getRhs s (rules g)) /\ nullableML g [NTS s] e`
     by METIS_TAC [EXISTS_MEM] THEN
ONCE_ASM_REWRITE_TAC [] THEN
`?e. MEM e (getRhs s (rules g)) /\ RTC (derives g) e []` by METIS_TAC [t4] THEN
Q.EXISTS_TAC `e` THEN
SRW_TAC [] []
`~(CARD (nonTerminals g) < CARD (nonTerminals g))`  by DECIDE_TAC  THEN
`nullableML g [] e` by METIS_TAC []

val t5 = mk_thm ([], ``RTC (derives g) [NTS s] [] ==> (NTS s) IN nonTerminals g``)
`(NTS s) IN nonTerminals g` by METIS_TAC [t5] THEN

val t6 = mk_thm ([], 
``(nonTerminals g INTER set sn = {}) ==> (NTS s) IN nonTerminals g ==> ~MEM (NTS s) sn``)

SRW_TAC [] [] THEN
METIS_TAC [t3, APPEND, APPEND_NIL, t6],


`~nullableML g sn [NTS s]` by METIS_TAC [t1] THEN
METIS_TAC [t1, t2, nullableEq1, nullable, nullableML']
Cases_on `t` THEN SRW_TAC [] []


-----------------------------------------
cases s->[] in g
1.false
2.

trans g g' = takeout all rules containing the symbol NTS s.
card nts g' < card nts g

cases ~nullableML g' [] (getRhs s (rules g))

1. ==> ~RTC (derives g') getRhs []
   ==> ~RTC (derives g) s []

2. nullableML g' [] (getRhs s (rules g))
   ==> ~ EVERY ($~ o nullableML g [NTS s]) (getRhs s (rules g))
   ==> F

*)

val mlDir = ref ("./theoryML/");

val _ =
 let open EmitML
 in emitML (!mlDir)
   ("grammarDef",
    OPEN ["regexp", "list", "string", "num","set"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: DATATYPE `rule = rule of string => symbol list`
    :: DATATYPE `grammar = G of rule list => string`
    :: DEFN ruleLhs
    :: DEFN ruleRhs
    :: DEFN getRules
    :: DEFN nonTerminalsML
    :: DEFN rhsWithSym
    :: DEFN lhsWithLastSym
    :: DEFN rules
    :: DEFN startSym
    :: DEFN getRhs
    :: DEFN nullableML
    :: [])
 end;

val _ = export_theory ();
