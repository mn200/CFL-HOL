(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory
open pred_setTheory listLemmaTheory regexpTheory

val _ = new_theory "grammarDef";

(* 14/05/07 AB *)


(* PROBLEM WITH DEFINITION OF NONTERMINAL SYMBOLS !!!!!!!!!!!!
If A->BC is the only prod then it only chooses A as nonterminal,
and ignores BC as they don't occur on th lhs of any prods
*)

(* Change lists to sets. *)

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

open stringTheory pred_setTheory regexpTheory relationTheory listTheory

open BasicProvers
(* e.g. S -> E * E becomes (Node S [E, *, E]) *)
val _ = Hol_datatype `rule = rule of string => symbol list`; (*  # symbol list`;*)

(* ?? verifying whether the spec of the grammar is consistent *)
(* grammar = (V, T, P, S) *)
val _ = Hol_datatype `grammar = G of rule set => string`;

val rule_terminals_def = Define`
  rule_terminals (rule lhs rhs) = { tmnl | isTmnlSym tmnl /\ MEM tmnl rhs }
`

val rule_nonterminals_def = Define`
  rule_nonterminals (rule lhs rhs) = NTS lhs INSERT { nt | isNonTmnlSym nt /\ MEM nt rhs }
  (* how about 
       lhs INSERT { s | MEM (NTS s) rhs } *)
`

val is_word  = Define `is_word w = EVERY isTmnlSym w`

val rules_def = Define`rules (G p s) = p`

val startSym_def = Define `startSym (G p s) = s`;


val terminals = Define `terminals (G p s) = BIGUNION (IMAGE rule_terminals p)`

(*val terminals = Define `terminals g = {tmnl | ?l. rule l tmnl IN rules g /\ isTmnlSym tmnl}`*)
val nonTerminals = Define `
  nonTerminals (G p s) = NTS s INSERT BIGUNION (IMAGE rule_nonterminals p)`

(*val nonTerminals = Define `nonTerminals g = {NTS (startSym g)} UNION {NTS l | ?r. rule l r IN rules g}`*)

val allSyms = Define `allSyms g = nonTerminals g UNION terminals g`

val _ = overload_on ("set", ``LIST_TO_SET``);


val derives = Define `
  derives g lsl rsl = ?s1 s2 rhs lhs. (s1 ++ [NTS lhs] ++ s2 = lsl) /\ 
                                      (s1 ++ rhs ++ s2 = rsl) /\ 
                                      (rule lhs rhs IN rules g)`;

val gaw = Define `gaw g nt = ?w. RTC (derives g) [nt] w /\ EVERY isTmnlSym w`;

(* 
a string  (terminal list) is in L(G) iff 
1) the string consists solely of terminals
2) the string can be derived from start symbol
*)

val sforms_def = Define `sforms g = {tsl | (RTC (derives g) [NTS (startSym g)] tsl)}`; 


val language_def = Define `language g = { tsl | RTC (derives g) [NTS (startSym g)] tsl /\ EVERY isTmnlSym tsl }`






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
	``!lhs rhs g.rule lhs rhs IN rules g ==> derives g [NTS lhs] rhs``,
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
`!lhs rhs g.rule lhs rhs IN rules g ==> derives g [NTS lhs] rhs` by FULL_SIMP_TAC (srw_ss()) [res1]
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

val upgr_r11 = store_thm("upgr_r11",
``derives g [NTS lhs] [NTS rhs] ==> rule lhs [NTS rhs] IN rules g``,
SRW_TAC [] [derives,lreseq]
);


val upgr_r15 = store_thm("upgr_r15",
``!u v.RTC (derives g) u v ==> (u=s1++lhs'++s2) ==> rule lhs lhs' IN rules g ==> RTC (derives g) (s1++[NTS lhs]++s2) v``,
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
DISJ2_TAC THEN SRW_TAC [] [derives] THEN METIS_TAC [APPEND_ASSOC]
]
)


val upgr_r17 = store_thm("upgr_r17",
``! u v.RTC (derives g) u v ==> (u=x++y) ==> (?x' y'. ((v=x'++y') /\ RTC (derives g) x x' /\ RTC (derives g) y y' ))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(?x''.derives g x' x'' /\ (v'=x''++y')) \/ (?y''.derives g y' y'' /\ (v'=x'++y''))` by METIS_TAC [lemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]
])

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
   METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]]
)

val slemma1_4 = store_thm("slemma1_4",
``(NTS nt IN nonTerminals g) = (?rhs.rule nt rhs IN rules g \/ ?l p s.rule l (p++[NTS nt]++s) IN rules g \/ (nt=startSym g))``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules_def,startSym_def] THENL[
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def,INSERT_DEF] THEN METIS_TAC [rules_def,rgr_r9eq],
DISJ2_TAC THEN
Q.EXISTS_TAC `rule_nonterminals (rule nt rhs)` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def,rules_def,INSERT_DEF],
METIS_TAC []],
DISJ2_TAC THEN
Q.EXISTS_TAC `rule_nonterminals (rule l (p ++ [NTS nt] ++ s'))` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def,rules_def,INSERT_DEF,isNonTmnlSym_def],
METIS_TAC [rules_def]]
])

val slemma1_3 = store_thm("slemma1_3",
``~(NTS nt IN nonTerminals g) = (~(?rhs.rule nt rhs IN rules g) /\ ~(?l p s.rule l (p++[NTS nt]++s) IN rules g) /\ ~(nt=startSym g))``,
METIS_TAC [slemma1_4,DE_MORGAN_THM]
)

val _ = export_theory ();
