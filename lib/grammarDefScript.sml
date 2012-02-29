(* A theory about grammars *)

open HolKernel boolLib bossLib Parse BasicProvers

open stringTheory relationTheory listTheory arithmeticTheory Defn
containerTheory pred_setTheory

open pred_setTheory listLemmasTheory symbolDefTheory
containerLemmasTheory setLemmasTheory relationLemmasTheory

val _ = new_theory "grammarDef";

(*
Theory of context free grammar.
Based on Chapter 4, Hopcroft & Ullman.
*)
val _ = overload_on ("IN", ``MEM``);

(* e.g. S -> E * E becomes (Node S [E, *, E]) *)
val _ = Hol_datatype
`rule = rule of 'nts => ('nts,'ts) symbol list`;
(*
val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 550),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,1)],
                  term_name = "rule"};
*)


(* grammar = (V, T, P, S) *)
val _ = Hol_datatype
`grammar = G of ('nts,'ts)rule list => 'nts`;

val ruleRhs = Define `ruleRhs (rule l r) = r`;

val ruleLhs = Define `ruleLhs (rule l r) = l`;

val _ = export_rewrites ["ruleLhs_def", "ruleRhs_def"];

val EXISTS_rule = store_thm(
  "EXISTS_rule",
  ``(∃r. P r) = (∃N rhs. P (rule N rhs))``,
  SRW_TAC [][EQ_IMP_THM]
  THENL [
	 Cases_on `r` THEN METIS_TAC [],
	 METIS_TAC []]);


val getRules = Define `
   (getRules sym [] = []) ∧
   (getRules sym ((rule l r)::rs) =
    if (sym = l) then
        rule l r :: getRules sym rs
    else getRules sym rs)`;


val rule_terminals = Define
`rule_terminals (rule l r) =
    { tmnl | isTmnlSym tmnl ∧ MEM tmnl r }`;

val rule_nonterminals = Define
`rule_nonterminals (rule l r) =
          NTS l INSERT { nt | isNonTmnlSym nt ∧ MEM nt r }`;

val is_word  = Define `is_word w = EVERY isTmnlSym w`;

val rules = Define `rules (G p s) = p`;

val startSym = Define `startSym (G p s) = s`;


val terminals = Define
`terminals (G p s) =
    BIGUNION (IMAGE rule_terminals (set p))`;

val nonTerminals = Define
`nonTerminals (G p s) =
  NTS s INSERT BIGUNION (IMAGE rule_nonterminals (set p))`;


val terminalsList = Define
`(terminalsList [] = []) ∧
 (terminalsList (rule l r::rst) =
      MAP ts2str (FILTER isTmnlSym r) ++ terminalsList rst)`;

val nonTmnls = Define
`(nonTmnls  [] = []) ∧
 (nonTmnls (rule l r::rst) =
      l::MAP nts2str (FILTER isNonTmnlSym r) ++ nonTmnls rst)`;


val nonTerminalsList = Define
`nonTerminalsList s rl = s::nonTmnls rl`;




val allSyms = Define
`allSyms g = nonTerminals g ∪ terminals g`;



val derives_def = Define`
  derives g lsl rsl = ∃s1 s2 rhs lhs.
			 (s1 ++ [NTS lhs] ++ s2 = lsl) ∧
                         (s1 ++ rhs ++ s2 = rsl) ∧
                         (MEM (rule lhs rhs) (rules g))
`;

val lderives = Define
`lderives g lsl rsl = ∃s1 s2 rhs lhs.
			  (s1 ++ [NTS lhs] ++ s2 = lsl) ∧
			  EVERY isTmnlSym s1 ∧
                          (s1 ++ rhs ++ s2 = rsl) ∧
                          (MEM (rule lhs rhs) (rules g))`;


val rderives = Define
`rderives g lsl rsl = ∃s1 s2 rhs lhs.
			  (s1 ++ [NTS lhs] ++ s2 = lsl) ∧
			  EVERY isTmnlSym s2 ∧
                          (s1 ++ rhs ++ s2 = rsl) ∧
                          (MEM (rule lhs rhs) (rules g))`;


val gaw = Define
`gaw g nt = ∃w. RTC (derives g) [nt] w ∧ EVERY isTmnlSym w`;


val sforms = Define
`sforms g = {tsl | (RTC (derives g) [NTS (startSym g)] tsl)}`;


val language = Define
`language g = { tsl | RTC (derives g) [NTS (startSym g)] tsl ∧
		      EVERY isTmnlSym tsl }`;


val llanguage = Define
`llanguage g = { tsl | RTC (lderives g) [NTS (startSym g)] tsl ∧
		       EVERY isTmnlSym tsl }`;

val rlanguage = Define
`rlanguage g = { tsl | RTC (rderives g) [NTS (startSym g)] tsl ∧
                       EVERY isTmnlSym tsl }`;

val isCnf_def = Define
`isCnf g = ∀l r.MEM (rule l r) (rules g) ⇒
    ((LENGTH r = 2) ∧ EVERY isNonTmnlSym r) ∨
    ((LENGTH r = 1) ∧ EVERY isTmnlSym r)`;

val derives_same_append_left = store_thm
("derives_same_append_left",
``∀g u v.derives g u v ⇒ ∀x.derives g (x++u) (x++v)``,
  SRW_TAC [] [derives_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`x++s1`,`s2`,`rhs`,`lhs`] THEN
  SRW_TAC [] []);

val derives_same_append_right = store_thm
("derives_same_append_right",
``∀g u v.derives g u v ⇒ ∀x.derives g (u++x) (v++x)``,
SRW_TAC [] [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2++x`,`rhs`,`lhs`]
THEN SRW_TAC [] []);


val rtc_derives_same_append_left = store_thm ("rtc_derives_same_append_left",
        ``∀u v.RTC (derives g) u v ⇒ ∀x. RTC (derives g) (x++u) (x++v)``,
        HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
        METIS_TAC [relationTheory.RTC_RULES,derives_same_append_left]
);

val rtc_derives_same_append_right = store_thm ("rtc_derives_same_append_right",
        ``∀u v.RTC (derives g) u v ⇒ ∀x. RTC (derives g) (u++x) (v++x)``,
        HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
        METIS_TAC [relationTheory.RTC_RULES,derives_same_append_right]
);


val derives_append = store_thm ("derives_append",
  ``RTC (derives g) M N ∧ RTC (derives g) P Q ⇒
    RTC (derives g) (M ++ P) (N ++ Q)``,
  Q_TAC SUFF_TAC `∀x y. RTC (derives g) x y ⇒
                        ∀u v. RTC (derives g) u v ⇒
                              RTC (derives g) (x ++ u) (y ++ v)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THENL [
                METIS_TAC [rtc_derives_same_append_left],
                METIS_TAC [derives_same_append_right,RTC_RULES]]);


val res1 = store_thm ("res1",
        ``∀lhs rhs g.MEM (rule lhs rhs) (rules g) ⇒ derives g [NTS lhs] rhs``,
        SRW_TAC [] [derives_def] THEN
        MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`]
        THEN SRW_TAC [] []);



val res2 = store_thm ("res2",
``∀g a b.derives g a b ⇒ ∀c.derives g b c ⇒ RTC (derives g) a c``,
SRW_TAC [] [] THEN METIS_TAC [RTC_SUBSET,RTC_RTC]
);


val res3 = store_thm ("res3",
``∀g a b.derives g a b ⇒ ∀c.RTC (derives g) b c ⇒ RTC (derives g) a c``,
SRW_TAC [] [] THEN METIS_TAC [RTC_SUBSET,RTC_RTC]);


val slres = store_thm ("slres",
``(s1 ++ [NTS lhs] ++ s2 = [NTS s]) ⇒ (lhs=s)``,
Cases_on `s1` THEN SRW_TAC [] []);

val slres2 = store_thm ("slres2",
``(s1 ++ [NTS lhs] ++ s2 = [NTS s]) ⇒ (s1=[]) ∧ (s2=[])``,
Cases_on `s1` THEN SRW_TAC [] []);


val rgr_r8 = store_thm ("rgr_r8",
``(r=r1++[sym]++r2) ⇒ derives g [NTS l] r ⇒  (∃a b.derives g [NTS l] (a++[sym]++b))``,
METIS_TAC []
);






val upgr_r7 = store_thm("upgr_r7",
``∀u z.
    (derives g)^* u z ⇒ (u=x++y) ⇒
    ∃x' y'. (z=x'++y') ⇒ (derives g)^* x x' ∧ (derives g)^* y y'``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
  MAP_EVERY Q.EXISTS_TAC [`x`,`y`] THEN SRW_TAC [] [RTC_RULES,RTC_REFLEXIVE],
  FULL_SIMP_TAC (srw_ss()) [derives_def] THEN METIS_TAC []
]);


val lupgr_r7 = store_thm("lupgr_r7",
``∀u z.
     (lderives g)^* u z ⇒ (u=x++y) ⇒
     ∃x' y'. (z=x'++y') ⇒ (lderives g)^* x x' ∧ (lderives g)^* y y'``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
  MAP_EVERY Q.EXISTS_TAC [`x`,`y`] THEN SRW_TAC [] [RTC_RULES,RTC_REFLEXIVE],
  FULL_SIMP_TAC (srw_ss()) [lderives] THEN METIS_TAC []
]);

val upgr_r11 = store_thm("upgr_r11",
``derives g [NTS lhs] [NTS rhs] ⇒ MEM (rule lhs [NTS rhs]) (rules g)``,
SRW_TAC [] [derives_def,lreseq]
);

val lupgr_r11 = store_thm("lupgr_r11",
``lderives g [NTS lhs] [NTS rhs] ⇒ MEM (rule lhs [NTS rhs]) (rules g)``,
SRW_TAC [] [lderives,lreseq]
);


val upgr_r15 = store_thm("upgr_r15",
``∀u v.RTC (derives g) u v ⇒ (u=s1++lhs'++s2) ⇒ MEM (rule lhs lhs') (rules g) ⇒ RTC (derives g) (s1++[NTS lhs]++s2) v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THENL[
METIS_TAC [res1,rtc_derives_same_append_right,rtc_derives_same_append_left,RTC_SUBSET],
METIS_TAC [RTC_RULES_RIGHT1]
]);



val rtc_r1 = store_thm("rtc_r1",
``(derives g)^* s1 s2 ⇒ s1≠s2 ⇒ ∃sf. derives g s1 sf ∧ (derives g)^* sf s2``,
REWRITE_TAC [Once RTC_CASES1] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]
);

val upgr_r18 = store_thm("upgr_r18",
``derives g s s' ⇒ (∃pfx sfx.(s'=pfx++sfx) ∧ derives g s pfx)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1++rhs++s2`,`[]`] THEN
SRW_TAC [] [] THEN
METIS_TAC []
);


val lemma2 = store_thm("lemma2",
``∀s1 s2 s1' s2'.
     derives g (s1++s2) s ⇒
     (∃s1'. derives g s1 s1' ∧ (s=s1'++s2)) ∨
     (∃s2'.derives g s2 s2' ∧ (s=s1++s2'))``,
SRW_TAC [] [] THEN
RULE_ASSUM_TAC (REWRITE_RULE [derives_def]) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃l1 l2.((s1=s1'++[NTS lhs]++l1) ∧ (s2=l2) ∧ (s2'=l1++l2)) ∨ ((s2=l2++[NTS lhs]++s2') ∧ (s1=l1) ∧ (s1'=l1++l2))` by METIS_TAC [list_r6] THENL[
DISJ1_TAC THEN SRW_TAC [] [derives_def] THEN METIS_TAC [],
DISJ2_TAC THEN SRW_TAC [] [derives_def] THEN METIS_TAC [APPEND_ASSOC]])

val llemma2 = store_thm("llemma2",
``∀s1 s2 s1' s2'.
    lderives g (s1++s2) s ⇒
      (∃s1'.lderives g s1 s1' ∧ (s=s1'++s2)) ∨
      (∃s2'.lderives g s2 s2' ∧ (s=s1++s2'))``,
SRW_TAC [] [] THEN
RULE_ASSUM_TAC (REWRITE_RULE [lderives]) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃l1 l2.((s1=s1'++[NTS lhs]++l1) ∧ (s2=l2) ∧ (s2'=l1++l2)) ∨ ((s2=l2++[NTS lhs]++s2') ∧ (s1=l1) ∧ (s1'=l1++l2))`
by METIS_TAC [list_r6] THENL[
DISJ1_TAC THEN SRW_TAC [] [lderives] THEN METIS_TAC [],
DISJ2_TAC THEN SRW_TAC [] [lderives] THEN
MAP_EVERY Q.EXISTS_TAC [`l2`,`s2'`,`rhs`,`lhs`] THEN
FULL_SIMP_TAC (srw_ss()) []])


val upgr_r17 = store_thm("upgr_r17",
``∀ u v.RTC (derives g) u v ⇒ (u=x++y) ⇒ (∃x' y'. ((v=x'++y') ∧ RTC (derives g) x x' ∧ RTC (derives g) y y' ))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(∃x''.derives g x' x'' ∧ (v'=x''++y')) ∨ (∃y''.derives g y' y'' ∧ (v'=x'++y''))` by METIS_TAC [lemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]
])


val lupgr_r17 = store_thm("lupgr_r17",
``∀ u v.RTC (lderives g) u v ⇒ (u=x++y) ⇒ (∃x' y'. ((v=x'++y') ∧ RTC (lderives g) x x' ∧ RTC (lderives g) y y' ))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(∃x''.lderives g x' x'' ∧ (v'=x''++y')) ∨ (∃y''.lderives g y' y'' ∧ (v'=x'++y''))` by METIS_TAC [llemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]])


val upgr_r19 = store_thm("upgr_r19",
``∀ u v.RTC (derives g) u v ⇒ (u=x++y++z) ⇒ (∃x' y' z'. ((v=x'++y'++z') ∧ RTC (derives g) x x' ∧ RTC (derives g) y y' ∧ RTC (derives g) z z'))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THEN
` derives g (x' ++ (y' ++ z')) v' ⇒ (∃x''.derives g x' x'' ∧ (v'=x''++(y'++z'))) ∨ (∃y''.derives g (y'++z') y'' ∧ (v'=x'++y''))` by SRW_TAC [][lemma2,APPEND,APPEND_ASSOC] THEN
  ` derives g (x' ++ y' ++ z') v' =  derives g (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] THEN
  RES_TAC THENL[
  METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],

  RES_TAC THEN
`derives g (y' ++ z') y'' ⇒ (∃s1'.derives g y' s1' ∧ (y''=s1'++z')) ∨ (∃s2'.derives g z' s2' ∧ (y''=y'++s2'))` by METIS_TAC [lemma2] THEN
   RES_TAC THEN
   METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]])


val lupgr_r19 = store_thm("lupgr_r19",
``∀ u v.RTC (lderives g) u v ⇒ (u=x++y++z) ⇒ (∃x' y' z'. ((v=x'++y'++z') ∧ RTC (lderives g) x x' ∧ RTC (lderives g) y y' ∧
RTC (lderives g) z z'))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THEN
` lderives g (x' ++ (y' ++ z')) v' ⇒ (∃x''.lderives g x' x'' ∧ (v'=x''++(y'++z'))) ∨ (∃y''.lderives g (y'++z') y'' ∧ (v'=x'++y''))`
by SRW_TAC [][llemma2,APPEND,APPEND_ASSOC] THEN
  ` lderives g (x' ++ y' ++ z') v' =  lderives g (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] THEN
  RES_TAC THENL[
  METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],
  RES_TAC THEN
`lderives g (y' ++ z') y'' ⇒ (∃s1'.lderives g y' s1' ∧ (y''=s1'++z')) ∨ (∃s2'.lderives g z' s2' ∧ (y''=y'++s2'))`
by METIS_TAC [llemma2] THEN SRW_TAC [] [] THEN
   RES_TAC THEN
   METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]])


val slemma1_4 = store_thm("slemma1_4",
``(NTS nt IN nonTerminals g) =
      (∃rhs.MEM (rule nt rhs) (rules g) ∨
       ∃l p s.MEM (rule l (p++[NTS nt]++s))(rules g) ∨
       (nt=startSym g))``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules,startSym]
THENL[
Cases_on `x` THEN
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,INSERT_DEF] THEN
METIS_TAC [rules,rgr_r9eq],

FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules,startSym] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `rule_nonterminals (rule nt rhs)` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,rules,INSERT_DEF],
METIS_TAC []],

FULL_SIMP_TAC (srw_ss()) [nonTerminals,rules,startSym] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `rule_nonterminals (rule l' (p ++ [NTS nt] ++ s))` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals,rules,INSERT_DEF,isNonTmnlSym_def],
METIS_TAC [rules]]]);

val slemma1_4Tmnls = store_thm("slemma1_4Tmnls",
``(TS t IN terminals g) = ∃l p s.MEM (rule l (p++[TS t]++s)) (rules g)``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [terminals,rules,startSym]
THENL[
Cases_on `x` THEN
FULL_SIMP_TAC (srw_ss()) [rule_terminals,INSERT_DEF] THEN
METIS_TAC [rules,rgr_r9eq],

FULL_SIMP_TAC (srw_ss()) [terminals,rules,startSym] THEN
Q.EXISTS_TAC `rule_terminals (rule l' (p ++ [TS t] ++ s))` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rule_terminals,rules,INSERT_DEF,isTmnlSym_def],
METIS_TAC [rules]]]);


val slemma1_3 = store_thm("slemma1_3",
``~(NTS nt IN nonTerminals g) = (~(∃rhs.MEM (rule nt rhs) (rules g)) ∧ ~(∃l p s.MEM (rule l (p++[NTS nt]++s)) (rules g)) ∧ ~(nt=startSym g))``,
METIS_TAC [slemma1_4,DE_MORGAN_THM]);

val emptySetList = store_thm ("emptySetList",
``(({} = LIST_TO_SET l) = (l=[]))``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM] THEN METIS_TAC [listNotEmpty,rgr_r9eq])


val finiteNtsList = store_thm("finiteNtsList",
``∀s.FINITE s ⇒ ∀g.(s=(LIST_TO_SET (rules g))) ⇒ FINITE (nonTerminals g)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
Cases_on `g`  THEN SRW_TAC [] [nonTerminals] THENL[
FULL_SIMP_TAC (srw_ss()) [rules] THEN METIS_TAC [emptySetList,MEM]],
Cases_on `g`  THEN
SRW_TAC [] [nonTerminals] THEN
Cases_on `x` THEN
`FINITE (LIST_TO_SET l')` by METIS_TAC [finiteLists] THEN
SRW_TAC [] [rule_nonterminals] THEN
`{nt | isNonTmnlSym nt ∧ MEM nt l'} = {nt | isNonTmnlSym nt ∧ nt IN (LIST_TO_SET l')}` by SRW_TAC [] [SET_TO_LIST_IN_MEM] THEN
ASM_REWRITE_TAC [] THEN
`{nt | isNonTmnlSym nt ∧ nt IN (LIST_TO_SET l')} SUBSET (LIST_TO_SET l')` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]  THEN
METIS_TAC [SUBSET_FINITE]]);

val rt1 = prove (
``∀e r.(e ∈ rule_terminals r) ⇒ ¬(isNonTmnlSym e)``,
  Cases_on `e` THEN
  SRW_TAC [] [] THEN
  Cases_on `r` THEN
  FULL_SIMP_TAC (srw_ss()) [rule_terminals] THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def]);

val rt2 = prove(
  ``∀e. ¬isNonTmnlSym e ⇒ ∃r. e ∈ rule_terminals r``,
  GEN_TAC THEN
  `(∃t. e = TS t) ∨ (∃N. e = NTS N)` by (Cases_on `e` THEN SRW_TAC [][]) THEN
  SRW_TAC [] [] THENL [
    Q.EXISTS_TAC `rule l [TS t]` THEN
    SRW_TAC [] [rule_terminals, isTmnlSym_def],
    METIS_TAC [isNonTmnlSym_def]]);


val rt = store_thm ("rt",
``∀e.(∃r.e IN rule_terminals r) = ~(isNonTmnlSym e)``,
METIS_TAC [rt1,rt2,EQ_IMP_THM]);


val ntsNotInTmnls1 = store_thm ("ntsNotInTmnls1",
``∀nt.isNonTmnlSym nt ⇒ ~(nt IN terminals g)``,
Cases_on `nt` THEN
Cases_on `g` THEN
SRW_TAC [] [terminals] THEN
METIS_TAC [isNonTmnlSym_def,rt]);


val ntsNotInTmnls = store_thm ("ntsNotInTmnls",
``∀nt. NTS nt ∉ terminals g``,
Cases_on `g` THEN
SRW_TAC [] [terminals] THEN METIS_TAC [isNonTmnlSym_def,rt])


val rnt1 = store_thm ("rnt1",
``∀e r. e ∈ rule_nonterminals r ⇒ ¬isTmnlSym e``,
Cases_on `e` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [rule_nonterminals] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def]);


val rnt2 = prove(
  ``∀e. ~(isTmnlSym e) ⇒ ∃r.(e IN rule_nonterminals r)``,
  Cases_on `e` THEN
  SRW_TAC [][isTmnlSym_def, isNonTmnlSym_def, rule_nonterminals,
             EXISTS_rule, EXISTS_OR_THM]);

val rnt = store_thm ("rnt",
``∀e.(∃r.e IN rule_nonterminals r) = ~(isTmnlSym e)``,
METIS_TAC [rnt1,rnt2,EQ_IMP_THM]);

val tsNotInNonTmnls = store_thm ("tsNotInNonTmnls",
``∀ts.~((TS ts) IN (nonTerminals g))``,
Cases_on `g` THEN
SRW_TAC [] [nonTerminals] THEN
METIS_TAC [rnt,isTmnlSym_def]);


val allNtSymsInGr = store_thm("allNtSymsInGr",
``∀nt.((NTS nt) IN allSyms g) = (∃rhs.MEM (rule nt rhs) (rules g)) ∨ (∃l p s.MEM (rule l (p++[NTS nt]++s))(rules g))
∨ ((nt=startSym g))``,
Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [allSyms] THEN
METIS_TAC [slemma1_4,ntsNotInTmnls]);

val allTmSymsInGr = store_thm("allTmSymsInGr",
``∀ts.((TS ts) IN allSyms g) = ∃l p s.MEM (rule l (p++[TS ts]++s))(rules g)``,
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
Q.EXISTS_TAC `rule_terminals (rule l' (p++[TS ts]++s))` THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [rule_terminals] THEN
METIS_TAC [isTmnlSym_def],
METIS_TAC []]]);


val finiteTerminals = store_thm("finiteTerminals",
``∀s.FINITE s ⇒ ∀g.(s=(LIST_TO_SET(rules g))) ⇒ FINITE (terminals g)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
Cases_on `g`  THEN SRW_TAC [] [terminals] THENL[
FULL_SIMP_TAC (srw_ss()) [rules] THEN METIS_TAC [emptySetList,MEM]],
Cases_on `g`  THEN
SRW_TAC [] [terminals] THEN
Cases_on `x` THEN
`FINITE (LIST_TO_SET l')` by METIS_TAC [finiteLists] THEN
SRW_TAC [] [rule_terminals] THEN
`{tmnl | isTmnlSym tmnl ∧ MEM tmnl l'} = {tmnl | isTmnlSym tmnl ∧ tmnl IN (LIST_TO_SET l')}` by SRW_TAC [] [SET_TO_LIST_IN_MEM] THEN
ASM_REWRITE_TAC [] THEN
`{tmnl | isTmnlSym tmnl ∧ tmnl IN (LIST_TO_SET l')} SUBSET
(LIST_TO_SET l')` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]  THEN
METIS_TAC [SUBSET_FINITE]])

val finiteAllSyms = store_thm ("finiteAllSyms",
``∀s.FINITE s ⇒ ∀g.(s=(LIST_TO_SET(rules g))) ⇒ FINITE (allSyms g)``,
SRW_TAC [] [allSyms] THEN
METIS_TAC [finiteNtsList,finiteTerminals])

val nullable = Define `nullable g sl = RTC (derives g) sl []`;

val getRhs = Define `(getRhs l [] = []) ∧
(getRhs l ((rule l' r)::rs) = if (l=l') then ([r]++getRhs l rs) else getRhs l rs)`

val derivesNull = Define `(derivesNull g (TS ts) = T) ∧
(derivesNull g (NTS nt) = MEM (rule nt []) (rules g))`;

val numNonTmnls = Define
`(numNonTmnls [] = 0) ∧
(numNonTmnls (rule l r::rs) =
 1 + LENGTH (FILTER isNonTmnlSym r) + numNonTmnls rs)`;

val getRhsDistrib = store_thm ("getRhsDistrib",
``∀l1 l2.getRhs A (l1++l2) = getRhs A l1 ++ getRhs A l2``,
Induct_on `l1` THEN
SRW_TAC [] [getRhs] THEN
Cases_on `h` THEN
SRW_TAC [] [getRhs]);

val x_1 = store_thm ("x_1",
``MEM e (getRhs A (rules g)) = derives g [NTS A] e``,
SRW_TAC [] [EQ_IMP_THM]
THENL[
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rules] THEN
Induct_on `l` THENL[
SRW_TAC [] [getRhs],

SRW_TAC [] [] THEN
Cases_on `h` THEN
Cases_on `A=n` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs] THENL[
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`e`,`A`] THEN
SRW_TAC [] [],

METIS_TAC [],
METIS_TAC [getRhs]]],

FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
`getRhs A (r1++[rule A rhs]++r2) = getRhs A r1 ++ getRhs A [rule A rhs] ++ getRhs A r2` by METIS_TAC [getRhsDistrib,APPEND_ASSOC] THEN
ASM_REWRITE_TAC [] THEN
SRW_TAC [] [getRhs] THEN
METIS_TAC []]);

val notNullGetRhs_1 = store_thm ("notNullGetRhs_1",
``∀nt g.~(getRhs nt (rules g)=[]) ⇒ (∃r.MEM (rule nt r) (rules g))``,
SRW_TAC [] [] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules] THEN
Induct_on `l` THENL[
SRW_TAC [] [] THEN METIS_TAC [getRhs],
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs] THEN
METIS_TAC [getRhs]]);

val notNullGetRhs_2 = store_thm ("notNullGetRhs_2",
``(∃r.MEM (rule nt r) (rules g)) ⇒ ~(getRhs nt (rules g)=[])``,
SRW_TAC [] [] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules] THEN
Induct_on `l` THENL[
SRW_TAC [] [] THEN METIS_TAC [getRhs],
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs] THEN
SRW_TAC [] []])

val notNullGetRhs = store_thm ("notNullGetRhs",
``(∃r.MEM (rule nt r) (rules g)) = ~(getRhs nt (rules g)=[])``,
METIS_TAC [notNullGetRhs_1,notNullGetRhs_2])


val ntsInGr = store_thm ("ntsInGr",
``∀nt g.~(getRhs nt (rules g)=[]) ⇒ (NTS nt) IN (nonTerminals g)``,
METIS_TAC [slemma1_4,notNullGetRhs])

val nullableList = Hol_defn "nullableList" `
  (nullableML
     (g:('a,'b)grammar) (sn:('a,'b)symbol list) ([]:('a,'b)symbol list) = T) ∧
  (nullableML g sn [TS ts] = F) ∧
  (nullableML g sn [NTS A] = if (MEM (NTS A) sn) then F
                             else EXISTS (nullableML g (NTS A :: sn))
                                         (getRhs A (rules g))) ∧
  (nullableML g sn (s::ss) = nullableML g sn [s] ∧ nullableML g sn ss)
`


val (nullableML,nullable_ind) = tprove(
  nullableList,
  WF_REL_TAC `
   inv_image
     (measure (λ(g,sn). CARD (nonTerminals g DIFF LIST_TO_SET sn))
                            LEX
                        measure LENGTH)
     (λ(g,sn,syms).((g,sn),syms))
  ` THEN
  SRW_TAC [ARITH_ss] [] THEN
  `FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
  `FINITE (set sn)` by SRW_TAC [][] THEN
  `FINITE (NTS A INSERT set sn)` by SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [CARD_DIFF] THEN
  SRW_TAC [] [] THENL[
    `~(getRhs A (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `NTS A ∈ nonTerminals g` by METIS_TAC [ntsInGr] THEN
    `nonTerminals g ∩ (NTS A INSERT set sn) =
     (NTS A INSERT set sn) ∩ nonTerminals g`
        by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
    SRW_TAC [] [ADD1] THEN
    `(nonTerminals g INTER set sn) = (set sn INTER nonTerminals g)`
        by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    DECIDE_TAC,

    `~(getRhs A (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `(NTS A) ∈ (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `NTS A ∉ set sn` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
    `NTS A ∉ (nonTerminals g ∩ set sn)` by METIS_TAC [IN_INTER] THEN
    `nonTerminals g ≠ set sn` by METIS_TAC [] THEN
    `FINITE (nonTerminals g)`
        by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
    `FINITE (set sn)` by SRW_TAC [][] THEN
    `FINITE (NTS A INSERT set sn)` by SRW_TAC [][] THEN
    `CARD (nonTerminals g) - CARD (nonTerminals g INTER set sn) =
       CARD ((nonTerminals g) DIFF (set sn))` by METIS_TAC [CARD_DIFF] THEN
    ASM_REWRITE_TAC [] THEN
    `NTS A ∈ (nonTerminals g DIFF set sn)`
       by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
    `nonTerminals g DIFF set sn ≠ {}` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
    `CARD (nonTerminals g DIFF set sn) ≠ 0`
      by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
    DECIDE_TAC
  ])

val _ = save_thm ("nullableML",nullableML)
val _ = save_thm ("nullableML_ind",nullable_ind)


val lhsWithNullSfx = Define `
   (lhsWithNullSfx g [] = []) ∧
   (lhsWithNullSfx g ((l,sfx)::rst) = if (nullable g sfx) then
                                        ([NTS l]::lhsWithNullSfx g rst)
                                      else lhsWithNullSfx g rst)`

val sfxNotNull = Define `(sfxNotNull g [] = []) ∧
(sfxNotNull g ((l,sfx)::rst) = if ~(nullable g sfx) then (sfx::sfxNotNull g rst) else sfxNotNull g rst)`

val notTmnlDerives = store_thm("notTmnlDerives",
``∀l.~(derives g [TS s] l)``,
SRW_TAC [] [derives_def] THEN
DISJ1_TAC THEN
`~(MEM (NTS lhs) [TS s])` by SRW_TAC [] [] THEN
METIS_TAC [rgr_r9eq])

val notTlDerives = store_thm("notTlDerives",
``∀l.~(derives g (TS s::rst) [])``,
SRW_TAC [] [derives_def])

val notTmnlRtcDerives1 = store_thm ("notTmnlRtcDerives1",
``∀ts l.RTC (derives g) [TS ts] l ⇒ (l=[TS ts])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
METIS_TAC [notTmnlDerives])

val notTmnlRtcDerives2 = store_thm ("notTmnlRtcDerives2",
``∀tl l.(l=[TS ts]) ⇒ RTC (derives g) [TS ts] l``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1])

val notTmnlRtcDerives = store_thm ("notTmnlRtcDerives",
``∀tl l.RTC (derives g) [TS ts] l = (l=[TS ts])``,
METIS_TAC [notTmnlRtcDerives1,notTmnlRtcDerives2])

val n0_1 = store_thm ("n0_1",
``∀l1 l2.derives g l1 l2 ⇒ (MEM (TS ts) l1) ⇒ (MEM (TS ts) l2)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rgr_r9eq] THEN
`s1++[NTS lhs]++s2 = r1'++([TS ts] ++ r2')` by SRW_TAC [] [] THEN
`∃l1 l2. (r1' = s1 ++ [NTS lhs] ++ l1) ∧ ([TS ts]++r2' = l2) ∧ (s2 = l1 ++ l2) ∨
(([TS ts] ++ r2') = l2 ++ [NTS lhs] ++ s2) ∧ (r1' = l1) ∧ (s1 = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [] [] THENL[
METIS_TAC [APPEND_ASSOC],
`∃l1 l2.([TS ts] = l2' ++ [NTS lhs] ++ l1) ∧ (r2' = l2) ∧ (s2 = l1 ++ l2) ∨
(r2' = l2 ++ [NTS lhs] ++ s2) ∧ ([TS ts] = l1) ∧ (l2' = l1 ++ l2)` by METIS_TAC [list_r6] THENL[
`(l2'=[]) ∧ (l1=[]) ∧ ([TS ts] = [NTS lhs])` by METIS_TAC [lreseq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
METIS_TAC [APPEND_ASSOC]]]
)

val mem_r1 = store_thm ("mem_r1",
``∀l.~(l=[]) = ∃e.MEM e l``,
SRW_TAC [] [EQ_IMP_THM] THEN
Induct_on `l` THEN
SRW_TAC [] [] THEN
METIS_TAC [])



val notTlRtcDerives_r1 = store_thm ("notTlRtcDerives_r1",
``∀x y.RTC (derives g) x y ⇒ (∃ts.MEM (TS ts) x) ⇒ ~(y=[])``,
HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [] [] THENL[
ONCE_REWRITE_TAC [mem_r1] THEN METIS_TAC [],

RES_TAC THEN
METIS_TAC [n0_1]])

val notTlRtcDerives = store_thm ("notTlRtcDerives",
``∀tl l.~(RTC (derives g) (TS ts::rst) [])``,
SRW_TAC [] [] THEN
METIS_TAC [notTlRtcDerives_r1,MEM])

val n4_1 = store_thm ("n4_1",
``∀s1 s2.nullableML g sn (s1++s2) ⇒ (nullableML g sn s1 ∧ nullableML g sn s2)``,
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
``∀s1 s2. (nullableML g sn s1 ∧ nullableML g sn s2) ⇒ nullableML g sn (s1++s2)``,
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
``∀s1 s2.  nullableML g sn (s1++s2)= (nullableML g sn s1 ∧ nullableML g sn s2)``,
METIS_TAC [n4_1,n4_2])

val n5 = store_thm ("n5",
``RTC (derives g) [TS ts] [] = nullableML g sn [TS ts]``,
SRW_TAC [] [EQ_IMP_THM] THEN
METIS_TAC [nullableML,notTmnlRtcDerives]);

val R = ``inv_image
            (measure (λ(g,sn). CARD ((nonTerminals g) DIFF (LIST_TO_SET sn)))
                      LEX
             measure (λsyms : ('nts,'ts)symbol list. LENGTH syms))
            (λ(g,sn,syms).((g,sn),syms))``

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
  ``(nullableML g sn [] = T) ∧
    (nullableML g sn (TS x :: t) = F) ∧
    (nullableML g sn (NTS n :: t) =
       if MEM (NTS n) sn then F
       else
         EXISTS (nullableML g (NTS n :: sn)) (getRhs n (rules g)) ∧
         nullableML g sn t)``,
  SRW_TAC [][nullableML] THEN
  Cases_on `t` THEN SRW_TAC [boolSimps.ETA_ss][nullableML, CONJ_ASSOC]);

open rich_listTheory
val mnlist_lemma = prove(
  ``∀x e y a b. (x ++ [e] ++ y = a ++ b) ⇒
                IS_PREFIX x a ∨ IS_PREFIX a (x ++ [e])``,
  Induct THEN Cases_on `a` THEN SRW_TAC [][IS_PREFIX] THEN METIS_TAC []);

val derives_split_append0 = prove(
  ``∀x y. RTC (derives g) x y ⇒
          ∀x0 x1. (x = x0 ++ x1) ⇒
                  ∃y0 y1. (y = y0 ++ y1) ∧
                     RTC (derives g) x0 y0 ∧
                          RTC (derives g) x1 y1``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THENL [
    METIS_TAC [RTC_RULES],
    FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
    `IS_PREFIX s1 x0 ∨ IS_PREFIX x0 (s1 ++ [NTS lhs])`
        by METIS_TAC [mnlist_lemma]
    THENL [
      `∃x0'. s1 = x0 ++ x0'` by METIS_TAC [IS_PREFIX_APPEND] THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`x0`, `x0' ++ rhs ++ s2`] MP_TAC) THEN
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`y0`, `y1`] THEN
      `x1 = x0' ++ [NTS lhs] ++ s2`
          by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
      SRW_TAC [][] THEN
      METIS_TAC [derives_def, RTC_RULES],
      `∃s1'. s1 ++ [NTS lhs] ++ s1' = x0` by METIS_TAC [IS_PREFIX_APPEND] THEN
      SRW_TAC [][] THEN
      `s2 = s1' ++ x1` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`s1 ++ rhs ++ s1'`, `x1`] MP_TAC) THEN
      SRW_TAC [][] THEN
      METIS_TAC [derives_def, RTC_RULES]
    ]]);



val derives_split_append =
SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] derives_split_append0


val nullable_APPEND = store_thm(
  "nullable_APPEND",
  ``nullable g (x ++ y) = nullable g x ∧ nullable g y``,
  SRW_TAC [][nullable, EQ_IMP_THM] THENL [
    IMP_RES_TAC derives_split_append THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
    IMP_RES_TAC derives_split_append THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
    METIS_TAC [derives_append, APPEND]
  ]);


val nullableML_append = store_thm(
  "nullableML_append",
  ``nullableML g sn (l1 ++ l2) =
     nullableML g sn l1 ∧ nullableML g sn l2``,
  Induct_on `l1` THEN SRW_TAC[] [nullableML] THEN
  Cases_on `h` THEN SRW_TAC [][nullableML'] THEN
  METIS_TAC []);

val finite_nts = store_thm
("finite_nts",
  ``FINITE (nonTerminals g)``,
  Cases_on `g` THEN SRW_TAC [][nonTerminals] THEN
  Cases_on `x` THEN SRW_TAC [][rule_nonterminals] THEN
  POP_ASSUM (K ALL_TAC) THEN Induct_on `l'` THEN SRW_TAC [][] THEN
  SRW_TAC [boolSimps.DNF_ss][GSPEC_OR] THEN
  SRW_TAC [][GSPEC_AND] THEN
  METIS_TAC [FINITE_INSERT, FINITE_EMPTY, INTER_FINITE, INTER_COMM]);

val nullableEq1 = store_thm ("nullableEq1",
  ``∀g sn l. nullableML g sn l ⇒ nullable g l``,
  HO_MATCH_MP_TAC R_IND THEN REPEAT STRIP_TAC THEN
  `(l = []) ∨ ∃h t. l = h::t` by (Cases_on `l` THEN SRW_TAC [][]) THEN
  SRW_TAC [][nullableML'] THEN1 SRW_TAC [][nullable] THEN
  `(∃tm. h = TS tm) ∨ (∃s. h = NTS s)` by (Cases_on `h` THEN SRW_TAC [][]) THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [nullableML'] THEN
  `nullable g t` by METIS_TAC [DECIDE ``x < SUC x``] THEN
  Q_TAC SUFF_TAC `nullable g [NTS s]` THEN1
        METIS_TAC [APPEND, nullable_APPEND] THEN
  `∃e. MEM e (getRhs s (rules g)) ∧ nullableML g (NTS s::sn) e`
     by METIS_TAC [EXISTS_MEM] THEN
  Q_TAC SUFF_TAC `nullable g e` THEN1
     METIS_TAC [x_1, nullable, RTC_RULES] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`g`, `NTS s :: sn`, `e`]
			      MP_TAC) THEN
  SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  `FINITE (nonTerminals g)` by METIS_TAC [finite_nts] THEN
  SRW_TAC [][] THENL [
    `NTS s ∈ nonTerminals g` by METIS_TAC [ntsInGr, mem_r1] THEN
    `nonTerminals g ∩ (NTS s INSERT set sn) =
       NTS s INSERT (nonTerminals g ∩ set sn)`
      by METIS_TAC [INTER_COMM, INSERT_INTER] THEN
    SRW_TAC [][] THEN DECIDE_TAC,
    Q_TAC SUFF_TAC `nonTerminals g ∩ set sn PSUBSET nonTerminals g`
          THEN1 METIS_TAC [CARD_PSUBSET, DECIDE ``x < y = 0 < y - x``] THEN
    SRW_TAC [][PSUBSET_DEF, EXTENSION] THEN
    METIS_TAC [ntsInGr, mem_r1]
  ]);

val n6 = store_thm ("n6",
``∀h tl.nullableML g ([]:('nts,'ts) symbol list) (h:('nts,'ts) symbol::tl) =
nullableML g ([]:('nts,'ts) symbol list) [h] ∧
nullableML g ([]:('nts,'ts) symbol list) tl ``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `tl` THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [nullableML])

val n3 = store_thm ("n3",
``∀s1 s2.nullableML g ([]:('nts,'ts) symbol list)
                      (s1:('nts,'ts) symbol list)
                ⇒
        nullableML g ([]:('nts,'ts) symbol list)
                     (s2:('nts,'ts) symbol list)
                ⇒
        nullableML g ([]:('nts,'ts) symbol list) (s1++s2)``,
SRW_TAC [] [] THEN
Induct_on `s1` THEN
SRW_TAC [] [] THEN
`nullableML g ([]:('nts,'ts) symbol list) [h] ∧
nullableML g ([]:('nts,'ts) symbol list) s1`
    by METIS_TAC [n4_1,APPEND] THEN
RES_TAC THEN
METIS_TAC [n6])



val lderivesImpDerives = store_thm ("lderivesImpDerives",
``∀x y.RTC (lderives g) x y ⇒
 EVERY isTmnlSym y ⇒
RTC (derives g) x y``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [lderives] THEN
METIS_TAC [derives_def, RTC_RULES])

val rderivesImpDerives = store_thm ("rderivesImpDerives",
``∀x y.RTC (rderives g) x y ⇒
EVERY isTmnlSym y ⇒
RTC (derives g) x y``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives] THEN
METIS_TAC [derives_def, RTC_RULES])


val drd = store_thm (
  "drd",
  ``∀l0 l1 l2. derives g l0 l1 ⇒ rderives g l1 l2 ⇒
               ∃l'. rderives g l0 l' ∧ derives g l' l2``,
  SRW_TAC [] [derives_def, rderives] THEN
  Q.MATCH_ASSUM_RENAME_TAC
      `pfx1 ++ rhs1 ++ sfx1 = pfx2 ++ [NTS N2] ++ sfx2` [] THEN
  Cases_on `isWord sfx1` THEN1 METIS_TAC [] THEN
  `∃x n y.(sfx1=x++[NTS n]++y) ∧ isWord y` by METIS_TAC [rightnt] THEN
  SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) []  THEN
  Q.ISPECL_THEN [`isTmnlSym`, `pfx1 ++ rhs1 ++ x`, `y`, `NTS n`,
                 `pfx2`, `sfx2`, `NTS N2`]
                MP_TAC (GEN_ALL listeq) THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
  SRW_TAC [][] THEN METIS_TAC [APPEND_ASSOC]);

val nrc_drd = store_thm ("nrc_drd",
``∀n l0 l1.NRC (derives g) (SUC n) l0 l1 ⇒
EVERY isTmnlSym l1 ⇒
∃l'.rderives g l0 l' ∧ NRC (derives g) n l' l1``,
Induct_on `n` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [derives_def, rderives] THEN
METIS_TAC [EVERY_APPEND],
METIS_TAC [NRC, drd]]);


val nrc_drdeq = store_thm ("nrc_drdeq",
``∀n l0 l1.NRC (derives g) n l0 l1 ⇒
EVERY isTmnlSym l1 ⇒
NRC (rderives g) n l0 l1``,
Induct_on `n` THEN SRW_TAC [] [] THEN
`∃l'.rderives g l0 l' ∧ NRC (derives g) n l' l1` by METIS_TAC [nrc_drd] THEN
`NRC (rderives g) n l' l1` by METIS_TAC [] THEN
METIS_TAC [NRC]);


val derivesImpRderives = store_thm ("derivesImpRderives",
``∀l0 l1.RTC (derives g) l0 l1 ⇒
EVERY isTmnlSym l1 ⇒ RTC (rderives g) l0 l1``,
METIS_TAC [nrc_drdeq, RTC_NRC, NRC_RTC]);

val drd_langeq = store_thm ("drd_langeq",
``∀g.language g = rlanguage g``,
SRW_TAC [] [EXTENSION, language, rlanguage, EQ_IMP_THM] THEN
METIS_TAC [derivesImpRderives, rderivesImpDerives]);

val ldres1 = store_thm ("ldres1",
        ``∀lhs rhs g.MEM (rule lhs rhs) (rules g) ⇒ lderives g [NTS lhs] rhs``,
        SRW_TAC [] [lderives] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`]
        THEN SRW_TAC [] []);

val lderives_same_append_left = store_thm
("lderives_same_append_left",
``∀g u v.lderives g u v ⇒ EVERY isTmnlSym x ⇒ lderives g (x++u) (x++v)``,
  SRW_TAC [] [lderives] THEN
MAP_EVERY Q.EXISTS_TAC [`x++s1`,`s2`,`rhs`,`lhs`]
THEN SRW_TAC [] []);

val lderives_same_append_right = store_thm
("lderives_same_append_right",
``∀g u v.lderives g u v ⇒ ∀x.lderives g (u++x) (v++x)``,
SRW_TAC [] [lderives] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2++x`,`rhs`,`lhs`]
THEN SRW_TAC [] []);

val rtc_lderives_same_append_left = store_thm
("rtc_lderives_same_append_left",
        ``∀u v.RTC (lderives g) u v ⇒ EVERY isTmnlSym x
              ⇒
	      RTC (lderives g) (x++u) (x++v)``,
        HO_MATCH_MP_TAC RTC_INDUCT THEN
        METIS_TAC [RTC_RULES,lderives_same_append_left]);

val rtc_lderives_same_append_right = store_thm
("rtc_lderives_same_append_right",
        ``∀u v.RTC (lderives g) u v
              ⇒
              RTC (lderives g) (u++x) (v++x)``,
        HO_MATCH_MP_TAC RTC_INDUCT THEN
        METIS_TAC [RTC_RULES,lderives_same_append_right]);

val drd_ld = store_thm ("drd_ld",
``∀l0 l1 l2.derives g l0 l1 ⇒
lderives g l1 l2 ⇒
∃l'.lderives g l0 l' ∧ derives g l' l2``,

FULL_SIMP_TAC (srw_ss()) [derives_def, lderives] THEN
SRW_TAC [][] THEN

Cases_on `isWord (s1++rhs++s2)` THEN1
(`isWord (s1' ++ [NTS lhs'] ++ s2')` by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
IMP_RES_TAC leftnt THEN
`EVERY isNonTmnlSym [NTS n]` by SRW_TAC [][isNonTmnlSym_def] THEN
`(l1 = s1') ∧([NTS n]++l2 = [NTS lhs']++s2')` by METIS_TAC [NOT_CONS_NIL,							    symlistdiv3] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[

`¬EVERY isTmnlSym  s1` by METIS_TAC [NOT_EVERY] THEN
IMP_RES_TAC leftnt THEN
SRW_TAC [][] THEN
`l1' ++ [NTS n] ++ (l2' ++ rhs ++ s2) = l1 ++ [NTS lhs'] ++ l2`
			by METIS_TAC [APPEND_ASSOC] THEN
`(l1' = l1) ∧ ([NTS n] ++ (l2' ++ rhs ++ s2) = [NTS lhs'] ++ l2)`
			by METIS_TAC [NOT_CONS_NIL, symlistdiv3, EVERY_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
METIS_TAC [NOT_EVERY, APPEND_ASSOC],

`¬EVERY isTmnlSym rhs` by METIS_TAC [NOT_EVERY] THEN
IMP_RES_TAC leftnt THEN SRW_TAC [][] THEN
Cases_on `isWord s1`
THENL[
      `(s1 ++ l1') ++ [NTS n] ++ (l2' ++ s2) = l1 ++ [NTS lhs'] ++ l2`
      by METIS_TAC [APPEND_ASSOC] THEN
      `isWord (s1++l1')` by SRW_TAC [][] THEN
      `(s1++l1' = l1) ∧ ([NTS n] ++ (l2' ++ s2) = [NTS lhs'] ++ l2)`
      by METIS_TAC [NOT_CONS_NIL, EVERY_DEF, symlistdiv3] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      METIS_TAC [NOT_EVERY, APPEND_ASSOC],

      `∃l1 n l2. (s1 = l1 ++ [NTS n] ++ l2) ∧ isWord l1` by METIS_TAC [leftnt] THEN
      SRW_TAC [][] THEN
      `l1'' ++ [NTS n'] ++ (l2'' ++ l1' ++ [NTS n] ++ l2' ++ s2) =
      l1 ++ [NTS lhs'] ++ l2` by METIS_TAC [APPEND_ASSOC] THEN
      `EVERY isNonTmnlSym [NTS n']` by SRW_TAC [][isNonTmnlSym_def] THEN
      `(l1''=l1) ∧ ([NTS n'] ++ (l2'' ++ l1' ++ [NTS n] ++ l2' ++ s2) =
		    [NTS lhs'] ++ l2)` by METIS_TAC [NOT_CONS_NIL,
							   symlistdiv3] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      METIS_TAC [NOT_EVERY, APPEND_ASSOC]
      ],

`¬EVERY isTmnlSym s2` by METIS_TAC [NOT_EVERY] THEN
IMP_RES_TAC leftnt THEN SRW_TAC [][] THEN
Cases_on `isWord s1`
THENL[
      Cases_on `isWord rhs`
      THENL[
	    `(s1 ++ rhs ++ l1') ++ [NTS n] ++ l2' = l1 ++ [NTS lhs'] ++ l2`
	    by METIS_TAC [APPEND_ASSOC] THEN
	    `isWord (s1++rhs++l1')` by SRW_TAC [][] THEN
	    `(s1++rhs++l1' = l1) ∧ ([NTS n] ++ l2' = [NTS lhs']++l2)`
	    by METIS_TAC [NOT_CONS_NIL, symlistdiv3, EVERY_DEF] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [NOT_EVERY, APPEND_ASSOC],

	    `∃l1 n l2. (rhs = l1 ++ [NTS n] ++ l2) ∧ isWord l1`
	    by METIS_TAC [leftnt]THEN
	    SRW_TAC [][] THEN
	    `(s1 ++ l1'') ++ [NTS n'] ++ (l2'' ++ l1' ++ [NTS n] ++ l2') =
	    l1 ++ [NTS lhs'] ++ l2` by METIS_TAC [APPEND_ASSOC] THEN
	    `isWord (s1++l1'')` by SRW_TAC [][] THEN
	    `(s1++l1'' = l1) ∧ ([NTS n'] ++ (l2'' ++ l1' ++ [NTS n] ++ l2') =
				[NTS lhs'] ++ l2)` by METIS_TAC [symlistdiv3,
								 NOT_CONS_NIL,
								 EVERY_DEF] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
	    METIS_TAC [NOT_EVERY, APPEND_ASSOC]
	    ],

      `∃l1 n l2. (s1 = l1 ++ [NTS n] ++ l2) ∧ isWord l1` by METIS_TAC [leftnt] THEN
      SRW_TAC [][] THEN
      `l1'' ++ [NTS n'] ++ (l2'' ++ rhs ++ l1' ++ [NTS n] ++ l2') =
      l1 ++ [NTS lhs'] ++ l2` by METIS_TAC [APPEND_ASSOC] THEN
      `EVERY isNonTmnlSym [NTS n']` by SRW_TAC [][isNonTmnlSym_def] THEN
      `(l1''=l1) ∧ ([NTS n'] ++ (l2'' ++ rhs ++ l1' ++ [NTS n] ++ l2') =
		    [NTS lhs'] ++ l2)` by METIS_TAC [NOT_CONS_NIL,
							   symlistdiv3] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      METIS_TAC [NOT_EVERY, APPEND_ASSOC]
      ]]);



val nrc_drd_ld = store_thm ("nrc_drd_ld",
``∀n l0 l1.NRC (derives g) (SUC n) l0 l1 ⇒
EVERY isTmnlSym l1 ⇒
∃l'.lderives g l0 l' ∧ NRC (derives g) n l' l1``,
Induct_on `n` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [derives_def, lderives] THEN
METIS_TAC [EVERY_APPEND],
METIS_TAC [NRC, drd_ld]]);


val nrc_drdeq_ld = store_thm ("nrc_drdeq_ld",
``∀n l0 l1.NRC (derives g) n l0 l1 ⇒
EVERY isTmnlSym l1 ⇒
NRC (lderives g) n l0 l1``,
Induct_on `n` THEN SRW_TAC [] [] THEN
`∃l'.lderives g l0 l' ∧ NRC (derives g) n l' l1` by METIS_TAC [nrc_drd_ld] THEN
`NRC (lderives g) n l' l1` by METIS_TAC [] THEN
METIS_TAC [NRC]);


val derivesImpLderives = store_thm ("derivesImpLderives",
``∀l0 l1.RTC (derives g) l0 l1 ⇒
EVERY isTmnlSym l1 ⇒ RTC (lderives g) l0 l1``,
METIS_TAC [nrc_drdeq_ld, RTC_NRC, NRC_RTC]);

val drd_ld_langeq = store_thm ("drd_ld_langeq",
``∀g.language g = llanguage g``,
SRW_TAC [] [EXTENSION, language, llanguage, EQ_IMP_THM] THEN
METIS_TAC [derivesImpLderives, lderivesImpDerives]);


val rtc2list_startSym_rtcRderives = store_thm
("rtc2list_startSym_rtcRderives",
``∀u v.RTC (rderives g) u v ⇒
(u=[NTS (startSym g)]) ⇒
∃dl.rtc2list (rderives g) dl ∧
     ((HD dl) = [NTS (startSym g)]) ∧ (LAST dl = v)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES, isTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
THENL[
      Q.EXISTS_TAC `[[NTS (startSym g)]]`  THEN
      SRW_TAC [] [rtc2list_def],

      Q.EXISTS_TAC `dl++[v']`  THEN
      SRW_TAC [] []
      THENL[

            METIS_TAC [rtc2list_append_right],

            Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [rtc2list_def]
            ]]);


val rtc2list_exists = store_thm ("rtc2list_exists",
  ``∀e. e ∈ language g ⇒
        ∃dl. rderives g ⊢ dl ◁ [NTS (startSym g)] → e``,
SRW_TAC [] [language, EXTENSION, listderiv_def] THEN
METIS_TAC [rtc2list_startSym_rtcRderives, derivesImpRderives])


val rsf = Define
`rsf g sf = RTC (rderives g) [NTS (startSym g)] sf`


val rsfDistribRtc2List = store_thm ("rsfDistribRtc2List",
``∀h t.rtc2list (rderives ag) (h::t) ⇒
rsf ag h ⇒ (∀e.MEM e t ⇒ rsf ag e)``,
Induct_on `t` THEN SRW_TAC [] [rtc2list_def] THEN
METIS_TAC [rsf, RTC_RULES, RTC_RTC])

val rderivesRtc2list = store_thm(
"rderivesRtc2list",
``∀dl.rderives ag h h' ⇒
       rtc2list (rderives ag) (h'::dl) ⇒
       rtc2list (rderives ag) (h::h'::dl)``,
Induct_on `dl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rtc2list_def])



val lemma2' = store_thm(
  "lemma2'",
  ``derives g
      (x ++ y) tgt =
      (∃x'. derives g x x' ∧ (tgt = x' ++ y)) ∨
      (∃y'. derives g y y' ∧ (tgt = x ++ y'))``,

  SRW_TAC [boolSimps.DNF_ss][derives_def, EQ_IMP_THM] THENL [
    Q.SPECL_THEN [`s1`, `x`, `y`, `lhs`, `s2`]
                 MP_TAC listCompLens THEN
    SRW_TAC [][] THEN
    METIS_TAC [APPEND_11, APPEND_ASSOC, APPEND_NIL],
    METIS_TAC [APPEND_NIL, APPEND_ASSOC],
    METIS_TAC [APPEND_NIL, APPEND_ASSOC]
  ]);

val upgr_r17_ld = store_thm
("upgr_r17_ld",
``∀dl x y v.(derives g) ⊢ dl ◁ u → v ⇒ (u=[x]++[y])
    ⇒
    (∃x' y' dl1 dl2. ((v=x'++y') ∧
		      (derives g) ⊢ dl1 ◁ [x] → x' ∧
		      (derives g) ⊢ dl2 ◁ [y] → y' ∧
		      (LENGTH dl1 ≤ LENGTH dl) ∧
		      (LENGTH dl2 ≤ LENGTH dl)))``,

  HO_MATCH_MP_TAC SNOC_INDUCT THEN
  SRW_TAC [][SNOC_APPEND, last_append] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  Cases_on `dl` THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN1
(MAP_EVERY Q.EXISTS_TAC [`[[x']]`,`[[y]]`] THEN
SRW_TAC [][]) THEN
SRW_TAC [][] THEN
`rtc2list (derives g) ([x'; y]::t)` by METIS_TAC [rtc2list_distrib_append_fst,
						  NOT_CONS_NIL, APPEND_ASSOC,
						  APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`([x'; y]::t) = FRONT ([x'; y]::t) ++ [(LAST dl1 ++ LAST dl2)]`
 by METIS_TAC [NOT_CONS_NIL, APPEND_FRONT_LAST] THEN
`FRONT ([x'; y]::t) ++ ([LAST dl1 ++ LAST dl2] ++[v])= ([x'; y]::(t ++ [v]))`
 by METIS_TAC [APPEND, APPEND_ASSOC] THEN
`rtc2list (derives g)  ([(LAST dl1 ++ LAST dl2)] ++ [v])`
 by METIS_TAC [rtc2list_distrib_append_snd, MEM, MEM_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
`(∃x'. derives g (LAST dl1) x' ∧ (v = x' ++ (LAST dl2))) ∨
    ∃y'. derives g (LAST dl2) y' ∧ (v = (LAST dl1) ++ y')`
 by METIS_TAC [lemma2'] THEN
SRW_TAC [][]
THENL[
      MAP_EVERY Q.EXISTS_TAC [`dl1++[x'']`,`dl2`] THEN
      SRW_TAC [][last_append]
      THENL[
	    METIS_TAC [rtc2list_append_right],
	    Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [],
	    FULL_SIMP_TAC (arith_ss) [],
	    FULL_SIMP_TAC (arith_ss) []
	    ],

      MAP_EVERY Q.EXISTS_TAC [`dl1`,`dl2++[y']`] THEN
      SRW_TAC [][last_append]
      THENL[
	    METIS_TAC [rtc2list_append_right],
	    Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [],
	    FULL_SIMP_TAC (arith_ss) [],
	    FULL_SIMP_TAC (arith_ss) []
	    ]
      ]);



val rtc2list_isolate_NT = store_thm(
  "rtc2list_isolate_NT",
  ``∀dl pfx N sfx.
    (derives g) ⊢ dl ◁ (pfx++[NTS N]++sfx) → LAST dl
      ⇒
    ∃pfx' rhs sfx'.(LAST dl = pfx'++rhs++sfx')
      ∧ ∃dl'. (derives g) ⊢ dl' ◁ [NTS N] → rhs ∧
              (LENGTH dl' <= LENGTH dl)``,
  HO_MATCH_MP_TAC SNOC_INDUCT THEN
  SRW_TAC [][SNOC_APPEND, last_append] THEN
  Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN1
     (MAP_EVERY Q.EXISTS_TAC [`pfx`, `[NTS N]`, `sfx`] THEN
      SRW_TAC [][] THEN Q.EXISTS_TAC `[[NTS N]]` THEN
      SRW_TAC [][]) THEN
  `rtc2list (derives g) dl`
     by METIS_TAC [rtc2list_distrib_append_fst] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `HD dl = pfx ++ [NTS N] ++ sfx`
     by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  RES_TAC THEN
  `dl ++ [x] = FRONT dl ++ [LAST dl; x]`
     by METIS_TAC [APPEND_FRONT_LAST, APPEND, APPEND_ASSOC] THEN
  `rtc2list (derives g) [LAST dl; x]`
     by METIS_TAC [rtc2list_distrib_append_snd, NOT_CONS_NIL] THEN
  `derives g (LAST dl) x` by FULL_SIMP_TAC (srw_ss()) [] THEN
  `(∃pfx2. derives g pfx'' pfx2 ∧ (x = pfx2 ++ rhs ++ sfx'')) ∨
   (∃rhs2. derives g rhs rhs2 ∧ (x = pfx'' ++ rhs2 ++ sfx'')) ∨
   (∃sfx2. derives g sfx'' sfx2 ∧ (x = pfx'' ++ rhs ++ sfx2))`
     by (Q.PAT_ASSUM `LAST dl = X` SUBST_ALL_TAC THEN
         FULL_SIMP_TAC (srw_ss()) [lemma2']) THEN
  SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`pfx2`, `LAST dl'`, `sfx''`] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `dl'` THEN SRW_TAC [ARITH_ss][],

    MAP_EVERY Q.EXISTS_TAC [`pfx''`, `rhs2`, `sfx''`] THEN
    SRW_TAC[][] THEN
    Q.EXISTS_TAC `dl' ++ [rhs2]` THEN
    SRW_TAC [][rtc2list_append_right] THEN
    Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    DECIDE_TAC,

    MAP_EVERY Q.EXISTS_TAC [`pfx''`, `LAST dl'`, `sfx2`] THEN
    SRW_TAC [][] THEN Q.EXISTS_TAC `dl'` THEN
    SRW_TAC [ARITH_ss][]
  ]);


val RTC_empty_nonrepeat_rule = prove(
  ``∀sf1 sf2.
       RTC (derives g) sf1 sf2 ⇒
       (sf2 = []) ⇒
       ~(sf1 = []) ⇒
       ∀N.  MEM (NTS N) sf1 ⇒
            ∃rhs. MEM (rule N rhs) (rules g) ∧
                  ~MEM (NTS N) rhs ∧
                  nullable g rhs``,
  HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
  Cases_on `sf1' = []` THENL [
    `(sf1 = [NTS N]) ∧ MEM (rule N []) (rules g)`
       by (FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	   SRW_TAC [][] THEN
	   FULL_SIMP_TAC (srw_ss()) []) THEN
    Q.EXISTS_TAC `[]` THEN
    SRW_TAC [][nullable, relationTheory.RTC_RULES],
    `∃M rhs pfx sfx.
        (sf1 = pfx ++ [NTS M] ++ sfx) ∧
        (sf1' = pfx ++ rhs ++ sfx) ∧
        MEM (rule M rhs) (rules g)`
      by METIS_TAC [derives_def] THEN
    Cases_on `MEM (NTS N) sf1'` THEN1 METIS_TAC [] THEN
    `M = N` by METIS_TAC [MEM_APPEND, MEM, symbol_11] THEN
    Q.EXISTS_TAC `rhs` THEN SRW_TAC [][] THENL [
      METIS_TAC [MEM_APPEND],
      METIS_TAC [nullable, nullable_APPEND]
    ]
  ]);

val LAST_APPEND_MID1 = prove(
  ``LAST (l1 ++ [e] ++ l2) = LAST (e::l2)``,
  Induct_on `l1` THEN SRW_TAC [][LAST_CONS_cond]);

val MEM_SPLIT_LIST = prove(
  ``MEM e l ==> ∃p s. l = p ++ [e] ++ s``,
  Induct_on `l` THEN SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] THEN SRW_TAC [][],
    RES_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h::p`, `s`] THEN SRW_TAC [][]
  ]);


val derivNts = Define `derivNts d = set (FLAT d)`;

val derivSubsetAppend =
store_thm ("derivSubsetAppend",
``∀d d'.(derivNts d ⊆ derivNts d') ⇒
  ∀p s.(derivNts d ⊆ (derivNts (p++d'++s)))``,
SRW_TAC [] [derivNts,FLAT_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]);


val derivSubsetAppendMem =
store_thm ("derivSubsetAppendMem",
``∀d d'.(derivNts d ⊆ derivNts d') ⇒
  ∀p s s' e.(derivNts (d++[e]) ⊆
                (derivNts (p++d'++[s++e++s'])))``,
SRW_TAC [] [derivNts,FLAT_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF,EXTENSION,UNION_DEF]);


val rtc2list_isolate_NT' = store_thm(
  "rtc2list_isolate_NT'",
  ``∀dl pfx N sfx.
    derives g ⊢ dl ◁ (pfx++[NTS N]++sfx) → LAST dl ⇒
    ∃pfx' rhs sfx'.(LAST dl = pfx'++rhs++sfx')
        ∧ ∃dl'. derives g ⊢ dl' ◁ [NTS N] → rhs ∧
        (LENGTH dl' ≤ LENGTH dl) ∧
        (derivNts dl' ⊆ derivNts dl)``,
  HO_MATCH_MP_TAC SNOC_INDUCT THEN
  SRW_TAC [][SNOC_APPEND, last_append] THEN
  Cases_on `dl=[]` THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN1
     (MAP_EVERY Q.EXISTS_TAC [`pfx`, `[NTS N]`, `sfx`] THEN
      SRW_TAC [][] THEN Q.EXISTS_TAC `[[NTS N]]` THEN
      SRW_TAC [][derivNts]) THEN
  `rtc2list (derives g) dl`
     by METIS_TAC [rtc2list_distrib_append_fst] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `HD dl = pfx ++ [NTS N] ++ sfx`
     by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  RES_TAC THEN
  `dl ++ [x] = FRONT dl ++ [LAST dl; x]`
     by METIS_TAC [APPEND_FRONT_LAST, APPEND, APPEND_ASSOC] THEN
  `rtc2list (derives g) [LAST dl; x]`
     by METIS_TAC [rtc2list_distrib_append_snd, NOT_CONS_NIL] THEN
  `derives g (LAST dl) x` by FULL_SIMP_TAC (srw_ss()) [] THEN
  `(∃pfx2. derives g pfx'' pfx2 ∧ (x = pfx2 ++ rhs ++ sfx'')) ∨
   (∃rhs2. derives g rhs rhs2 ∧ (x = pfx'' ++ rhs2 ++ sfx'')) ∨
   (∃sfx2. derives g sfx'' sfx2 ∧ (x = pfx'' ++ rhs ++ sfx2))`
     by (Q.PAT_ASSUM `LAST dl = X` SUBST_ALL_TAC THEN
         FULL_SIMP_TAC (srw_ss()) [lemma2']) THEN
  SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`pfx2`, `LAST dl'`, `sfx''`] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `dl'` THEN SRW_TAC [ARITH_ss][] THEN
    `(FRONT dl ++
       [pfx'' ++ LAST dl' ++ sfx''; pfx2 ++ LAST dl' ++ sfx'']) =
      dl ++ [pfx2 ++ LAST dl' ++ sfx'']`
	by METIS_TAC [APPEND_FRONT_LAST,APPEND] THEN
    METIS_TAC [derivSubsetAppend,APPEND_NIL],

    MAP_EVERY Q.EXISTS_TAC [`pfx''`, `rhs2`, `sfx''`] THEN
    SRW_TAC[][] THEN
    Q.EXISTS_TAC `dl' ++ [rhs2]` THEN
    SRW_TAC [][rtc2list_append_right] THENL[
      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [],
                                            DECIDE_TAC,
      `(FRONT dl ++
       [pfx'' ++ LAST dl' ++ sfx''; pfx'' ++ rhs2 ++ sfx'']) =
      dl ++ [pfx'' ++ rhs2 ++ sfx'']`
	by METIS_TAC [APPEND_FRONT_LAST,APPEND] THEN
      METIS_TAC [derivSubsetAppendMem,APPEND_NIL]
    ],

    MAP_EVERY Q.EXISTS_TAC [`pfx''`, `LAST dl'`, `sfx2`] THEN
    SRW_TAC [][] THEN Q.EXISTS_TAC `dl'` THEN
    SRW_TAC [ARITH_ss][] THEN
    `(FRONT dl ++
       [pfx'' ++ LAST dl' ++ sfx''; pfx'' ++ LAST dl' ++ sfx2]) =
      dl ++ [pfx'' ++ LAST dl' ++ sfx2]`
	by METIS_TAC [APPEND_FRONT_LAST,APPEND] THEN
    METIS_TAC [derivSubsetAppend,APPEND_NIL]
  ]);

val no_repeats = prove(
  ``derives g ⊢ d0 ◁ [NTS N] → [] ⇒
    ∃d. derives g ⊢ d ◁ [NTS N] → [] ∧
        derivNts d ⊆ derivNts d0 ∧ LENGTH d ≤ LENGTH d0 ∧
        ∀sf. MEM sf (TL d) ⇒ ~MEM (NTS N) sf``,
  completeInduct_on `LENGTH d0` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO] THEN
  Cases_on `∀sf. MEM sf (TL d0) ⇒ ~MEM (NTS N) sf`
    THEN1 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	   SRW_TAC [][] THEN
	   Q.EXISTS_TAC `d0` THEN
	   SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `¬(d0 = [])` by METIS_TAC [listderiv_def, rtc2list_def] THEN
  `∃d1. d0 = [NTS N]::d1` by METIS_TAC [list_CASES, HD, listderiv_def] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `∃h d2. (d1 = h::d2) ∧ derives g [NTS N] h ∧ derives g ⊢ d1 ◁ h → []`
     by (RULE_ASSUM_TAC (ONCE_REWRITE_RULE [listderiv_thm]) THEN
         FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]) THEN
  `∃l1 l2. d1 = l1 ++ [sf] ++ l2` by METIS_TAC [rgr_r9eq] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [ldAppend] THEN
  `∃p s. sf = p ++ [NTS N] ++ s` by METIS_TAC [rgr_r9eq] THEN
  `∃dl'. derives g ⊢ dl' ◁ [NTS N] → [] ∧ LENGTH dl' ≤ LENGTH (sf::l2) ∧
         derivNts dl' ⊆ derivNts (sf::l2)`
    by METIS_TAC [rtc2list_isolate_NT',HD,listderiv_def,APPEND_eq_NIL] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `dl'` MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `dl''` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `dl''` THEN
  Q.PAT_ASSUM `XX = h::d2` (ASSUME_TAC o SYM) THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [derivNts] THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
  Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [APPEND_EQ_SING] THEN
  SRW_TAC [][FLAT_APPEND] THEN METIS_TAC []);

val derivNtsMem =
store_thm ("derivNtsMem",
``∀dl e.e ∈ derivNts dl  = ∃l.MEM  l dl ∧ MEM e l``,
Induct_on `dl` THEN SRW_TAC [] [derivNts,EQ_IMP_THM] THEN
METIS_TAC [derivNts,mem_in]);

val nullableMLEq = store_thm (
  "nullableMLEq",
  ``∀g sn l. nullableML g sn l =
        ∀e. MEM e l ⇒ isNonTmnlSym e ∧ nullableML g sn [e]``,
  Induct_on `l` THEN SRW_TAC [][nullableML'] THEN
  Cases_on `h` THEN SRW_TAC [] [nullableML'] THEN
  SRW_TAC [boolSimps.DNF_ss][EXISTS_MEM, isNonTmnlSym_def, nullableML'] THEN
  METIS_TAC []);

val rtc2listTlHd =
store_thm ("rtc2listTlHd",
``∀dl. derives g ⊢ dl ◁ HD dl → [] ⇒
 (LENGTH (TL dl) > 1) ⇒
 ∃pfx N sfx.HD (TL dl) = pfx++[NTS N]++sfx``,
 Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `t` THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
METIS_TAC []);



val rtc2listTlHdEveryMem =
store_thm ("rtc2listTlHdEveryMem",
``∀dl. derives g ⊢ dl ◁ HD dl → [] ⇒
   (LENGTH (TL dl) > 1) ⇒
    ∀e.MEM e (HD (TL dl)) ⇒ isNonTmnlSym e``,
SRW_TAC [][listderiv_def] THEN
`~(dl=[])` by (Cases_on `dl` THEN
	       FULL_SIMP_TAC (srw_ss()) []) THEN
`RTC (derives g) (HD dl) []` by METIS_TAC [rtc2listRtcHdLast] THEN
`dl=[HD dl]++TL dl` by METIS_TAC [listHdTl] THEN
`~(TL dl =[])`
    by (Cases_on `TL dl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
`rtc2list (derives g) (TL dl)`
    by METIS_TAC [rtc2list_distrib_append_snd] THEN
`LAST (TL dl) =[]` by METIS_TAC [last_append,APPEND_FRONT_LAST] THEN
`RTC (derives g) (HD (TL dl)) []`
    by METIS_TAC [rtc2listRtcHdLast] THEN
`RTC (derives g) [e] []` by METIS_TAC [nullable,nullable_APPEND,rgr_r9eq] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
METIS_TAC [notTmnlRtcDerives,NOT_CONS_NIL]);


val nmlEq' = store_thm ("nmlEq'",
``∀l.nullableML g sn l = ∀e.MEM e l ⇒ nullableML g sn [e]``,
Induct_on `l` THEN SRW_TAC [][nullableML]  THEN
Cases_on `h` THEN
SRW_TAC [][nullableML']  THEN
METIS_TAC [nullableML']);


val derivTlSubset =
store_thm ("derivTlSubset",
``∀dl. ~(dl=[]) ⇒ derivNts (TL dl) SUBSET (derivNts dl)``,
Induct_on `dl` THEN
SRW_TAC [][derivNts]);

val derivNtsNotMem = store_thm
("derivNtsNotMem",
``∀e dl.  (∀l.MEM l dl ⇒ ~MEM e l) ⇒ ~(e IN derivNts dl)``,
Induct_on `dl` THEN
SRW_TAC [][derivNts] THEN
Cases_on `dl=[]` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [flatMemNot]);

val listderiv_NIL = prove(
  ``R ⊢ [] ◁ x → y = F``,
  SRW_TAC [][listderiv_def]);

val split_derivations_horizontally = store_thm(
  "split_derivations_horizontally",
  ``∀d sf1 sf2.
       derives g ⊢ d ◁ (sf1 ++ sf2) → sf ⇒
       ∃d1 d2 rsf1 rsf2.
          (sf = rsf1 ++ rsf2) ∧
          LENGTH d1 ≤ LENGTH d ∧ LENGTH d2 ≤ LENGTH d ∧
          derivNts d1 ⊆ derivNts d ∧ derivNts d2 ⊆ derivNts d ∧
          derives g ⊢ d1 ◁ sf1 → rsf1 ∧
          derives g ⊢ d2 ◁ sf2 → rsf2``,
  Induct_on `d` THEN SRW_TAC [][listderiv_NIL, listderiv_thm] THEN1
    (MAP_EVERY Q.EXISTS_TAC [`[sf1]`, `[sf2]`, `sf1`, `sf2`] THEN
     SRW_TAC [][listderiv_thm, derivNts]) THEN
  `∃s1 s2 N rhs.
      (s1 ++ [NTS N] ++ s2 = sf1 ++ sf2) ∧ (s1 ++ rhs ++ s2 = h') ∧
      rule N rhs ∈ rules g` by METIS_TAC [derives_def] THEN
  `(∃l2. (sf1 = s1 ++ [NTS N] ++ l2) ∧ (s2 = l2 ++ sf2)) ∨
   ∃l1. (s1 = sf1 ++ l1) ∧ (sf2 = l1 ++ [NTS N] ++ s2)`
      by METIS_TAC [list_r6]
  THENL [
    FIRST_X_ASSUM (Q.SPECL_THEN [`s1 ++ rhs ++ l2`, `sf2`] MP_TAC) THEN
    REPEAT VAR_EQ_TAC THEN FULL_SIMP_TAC (srw_ss()) [derivNts] THEN
    STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`(s1 ++ [NTS N] ++ l2) :: d1`, `d2`,
                            `rsf1`, `rsf2`] THEN
    Tactical.REVERSE (SRW_TAC[ARITH_ss][SUBSET_DEF]) THEN1
      (SRW_TAC [][listderiv_thm] THEN DISJ2_TAC THEN
       Q.EXISTS_TAC `s1 ++ rhs ++ l2` THEN
       SRW_TAC [][derives_def] THEN
       Cases_on `d1` THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC[],

    FIRST_X_ASSUM (Q.SPECL_THEN [`sf1`, `l1 ++ rhs ++ s2`] MP_TAC) THEN
    REPEAT VAR_EQ_TAC THEN FULL_SIMP_TAC (srw_ss()) [derivNts] THEN
    STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`d1`, `(l1 ++ [NTS N] ++ s2)::d2`,
                            `rsf1`, `rsf2`] THEN
    Tactical.REVERSE (SRW_TAC[ARITH_ss][SUBSET_DEF]) THEN1
      (SRW_TAC [][listderiv_thm] THEN DISJ2_TAC THEN
       Q.EXISTS_TAC `l1 ++ rhs ++ s2` THEN
       SRW_TAC [][derives_def] THEN
       Cases_on `d2` THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC[]
  ]);

val derives_NIL_split = prove(
  ``derives g ⊢ d ◁ sf → [] ⇒
    ∀s. s ∈ sf ⇒
        ∃N d'. (s = NTS N) ∧
               derives g ⊢ d' ◁ [NTS N] → [] ∧
               LENGTH d' ≤ LENGTH d ∧
               derivNts d' ⊆ derivNts d ∧
               ∀sf'. sf' ∈ TL d' ⇒ NTS N ∉ sf'``,
  REPEAT STRIP_TAC THEN
  `∃pfx sfx. sf = pfx ++ [s] ++ sfx` by METIS_TAC [rgr_r9eq] THEN
  `∃d10 d2. LENGTH d10 ≤ LENGTH d ∧ LENGTH d2 ≤ LENGTH d ∧
            derivNts d10 ⊆ derivNts d ∧ derivNts d2 ⊆ derivNts d ∧
            derives g ⊢ d10 ◁ (pfx ++ [s]) → [] ∧
            derives g ⊢ d2 ◁ sfx → []`
     by METIS_TAC [split_derivations_horizontally, APPEND_eq_NIL] THEN
  `∃d1 ds. LENGTH d1 ≤ LENGTH d10 ∧ LENGTH ds ≤ LENGTH d10 ∧
           derivNts d1 ⊆ derivNts d10 ∧ derivNts ds ⊆ derivNts d10 ∧
           derives g ⊢ d1 ◁ pfx → [] ∧
           derives g ⊢ ds ◁ [s] → []`
     by METIS_TAC [split_derivations_horizontally, APPEND_eq_NIL] THEN
  Tactical.REVERSE (Cases_on `s`) THEN1
     (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      IMP_RES_TAC rtc2listRtcHdLast THEN
      METIS_TAC [notTmnlRtcDerives, NOT_NIL_CONS]) THEN
  SRW_TAC [][] THEN METIS_TAC [no_repeats, SUBSET_TRANS, LESS_EQ_TRANS]);

val nullableSingNt = store_thm (
  "nullableSingNt",
  ``∀N sn.
      derives g ⊢ dl ◁ [NTS N] → [] ⇒
      (derivNts dl ∩ set sn = {}) ⇒
      (∀sf. MEM sf (TL dl) ⇒ ~MEM (NTS N) sf) ⇒
      nullableML g sn [NTS N]``,
  completeInduct_on `LENGTH dl` THEN
  FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO] THEN
  SRW_TAC [][] THEN
  SRW_TAC [][nullableML'] THEN1
    (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
     Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
     FULL_SIMP_TAC (srw_ss()) [derivNts, EXTENSION] THEN METIS_TAC []) THEN
  Cases_on `dl` THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_NIL, listderiv_thm] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [GSYM x_1] THEN
  SIMP_TAC (srw_ss()) [EXISTS_MEM] THEN Q.EXISTS_TAC `h'` THEN
  SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [nullableMLEq] THEN
  GEN_TAC THEN STRIP_TAC THEN
  `∃N d'. (e = NTS N) ∧ derives g ⊢ d' ◁ [NTS N] → [] ∧
          LENGTH d' ≤ LENGTH (h'::t') ∧ derivNts d' ⊆ derivNts (h'::t') ∧
          ∀sf. sf ∈ TL d' ⇒ NTS N ∉ sf`
    by METIS_TAC [derives_NIL_split] THEN
  SRW_TAC [][isNonTmnlSym_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `d'` THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
  Cases_on `d'` THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_NIL, derivNts] THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF, MEM_FLAT] THEN
  METIS_TAC []);

val derivNtsNullable = store_thm (
  "derivNtsNullable",
  ``∀dl x. derives g ⊢ dl ◁ x → [] ⇒
           ∀sym. sym IN derivNts dl ⇒ RTC (derives g) [sym] []``,
  Induct_on `dl` THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [derivNts] THEN
  Cases_on `dl=[]` THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `LAST dl = []` by METIS_TAC [last_append,APPEND] THEN
  `RTC (derives g) h []`
      by METIS_TAC [rtc2listRtcHdLast,HD,NOT_CONS_NIL]
  THENL[
    METIS_TAC [nullable,nullable_APPEND,rgr_r9eq],
    METIS_TAC [APPEND,rtc2list_distrib_append_snd]
  ]);

val nullableImpML = store_thm (
  "nullableImpML",
  ``∀l. nullable g l ⇒
        ∀sn. (∀sym. MEM sym sn ⇒ ~nullable g [sym]) ⇒
             nullableML g sn l``,
  Induct_on `l` THEN SRW_TAC [][nullableML'] THEN
  `(∃s. h = TS s) ∨ (∃s. h = NTS s)`
     by (Cases_on `h` THEN SRW_TAC [][]) THEN
  SRW_TAC [] [nullableML']
  THENL[
        METIS_TAC [notTmnlRtcDerives,APPEND,nullable_APPEND,
  		   NOT_CONS_NIL,nullable],

        METIS_TAC [notTmnlRtcDerives,APPEND,nullable_APPEND,
  		   NOT_CONS_NIL,nullable],

        `nullable g [NTS s]`
	    by METIS_TAC [nullable_APPEND,APPEND] THEN
        FULL_SIMP_TAC (srw_ss()) [nullable] THEN
        `∃d0. derives g ⊢ d0 ◁ [NTS s] → []`
	    by METIS_TAC [rtc2list_exists'] THEN
	`¬(d0=[])` by METIS_TAC [listderiv_def,rtc2list_def] THEN
        `∃d. derives g ⊢ d ◁ [NTS s] → [] ∧
           derivNts d ⊆ derivNts d0 ∧
           LENGTH d ≤ LENGTH d0 ∧
           ∀sf. MEM sf (TL d) ⇒ ~MEM (NTS s) sf`
              by METIS_TAC [no_repeats] THEN
	`(derives g)^* l []`
	    by METIS_TAC [nullable,nullable_APPEND,APPEND] THEN
        `derivNts d INTER set sn = {}`
           by SRW_TAC [][] THEN
        `~(d=[])` by METIS_TAC [rtc2list_def,listderiv_def]
        THENL[
  	      `∀sym.sym IN derivNts d ⇒ RTC (derives g) [sym] []`
  	    by METIS_TAC [derivNtsNullable,listderiv_def] THEN
  	    FULL_SIMP_TAC (srw_ss()) [INTER_DEF,EXTENSION] THEN
  	    METIS_TAC [mem_in],
  	    METIS_TAC [nullableML',nullableSingNt]
  	    ],

        METIS_TAC [APPEND,nullable_APPEND]
        ]);

val nullableEq2 = store_thm ("nullableEq2",
  ``∀g sn l.nullable (g:('a, 'b) grammar) l
   ⇒ (sn=[]:('a, 'b) symbol list) ⇒ nullableML g sn l``,
SRW_TAC [][] THEN
METIS_TAC [MEM,nullableImpML])

val nullableEq = store_thm ("nullableEq",
``∀g l.nullable g l =
nullableML (g:('a, 'b) grammar) ([]:('a, 'b) symbol list) l``,
METIS_TAC [nullableEq1, nullableEq2]);

val list_neq = store_thm ("list_neq",
``∀st n.~(st=n) ⇒ ~∃pfx sfx.[NTS st] = pfx++[NTS n]++sfx``,
SRW_TAC [] [] THEN
Induct_on `pfx` THEN SRW_TAC [] []);

val list_isp = store_thm ("list_isp",
``∀s1' s2' N l.(s1' ++ s2' = pfx ++ [NTS N] ++ l) ⇒
EVERY isTmnlSym s2' ⇒ EVERY isTmnlSym l ⇒
IS_PREFIX s1' (pfx ++ [NTS N])``,
Induct_on `pfx` THEN SRW_TAC [] []
THENL[
Cases_on `s1'` THEN SRW_TAC [] [] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, IS_PREFIX],

Cases_on `s1'` THEN SRW_TAC [] []
THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
METIS_TAC [IS_PREFIX, IS_PREFIX_REFL],
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
METIS_TAC [IS_PREFIX, IS_PREFIX_REFL]]]);

val rdImpDg = store_thm ("rdImpDg",
``∀u v.rderives g u v ⇒ derives g u v``,
SRW_TAC [] [derives_def, rderives] THEN
METIS_TAC [])

val rtcRdImpDg = store_thm ("rtcRdImpDg",
``∀u v.RTC (rderives g) u v ⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RULES, rdImpDg])

val rtcRderivesLastTmnl = store_thm ("rtcRderivesLastTmnl",
``∀u v.RTC (rderives g) u v ⇒ (u=(pfx++[TS ts])) ⇒ ∃pfx'.(v=pfx'++[TS ts])``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives] THEN
Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`LAST (s1 ++ [NTS lhs] ++ h::t) = TS ts` by METIS_TAC [last_elem, APPEND, APPEND_ASSOC] THEN
`LAST (h::t) = TS ts` by METIS_TAC [last_append, NOT_CONS_NIL] THEN
`LAST v' = TS ts` by METIS_TAC [last_append, NOT_CONS_NIL, APPEND, APPEND_ASSOC] THEN
`~(v'=[])` by SRW_TAC [] [] THEN
METIS_TAC [lastListBdown]);

val rderives_has_tmnl = store_thm ("rderives_has_tmnl",
``∀x x'.rderives g x x' ⇒ MEM (TS h) x ⇒ MEM (TS h) x'``,
SRW_TAC [] [rderives] THEN
FULL_SIMP_TAC (srw_ss()) []);


val rtc_rderives_has_tmnl = store_thm ("rtc_rderives_has_tmnl",
``∀x y.RTC (rderives g) x y ⇒ MEM (TS h) x ⇒ MEM (TS h) y``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [] THEN
METIS_TAC [rderives_has_tmnl]);

val rdres1 = store_thm ("rdres1",
        ``∀lhs rhs g.MEM (rule lhs rhs) (rules g) ⇒ rderives g [NTS lhs] rhs``,
        SRW_TAC [] [rderives] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`]
        THEN SRW_TAC [] []);

val rderives_append = store_thm ("rderives_append",
``∀nt r.rderives g [NTS nt] r ⇒ ∀sfx.EVERY isTmnlSym sfx ⇒
∀pfx.rderives g (pfx++[NTS nt]++sfx) (pfx++r++sfx)``,
SRW_TAC [] [rderives] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`pfx`,`sfx`,`rhs`,`lhs`]  THEN
METIS_TAC []);

val rderives_same_append_left = store_thm ("rderives_same_append_left",
        ``∀g u v.rderives g u v ⇒ ∀x.rderives g (x++u) (x++v)``,
        SRW_TAC [] [rderives] THEN MAP_EVERY Q.EXISTS_TAC [`x++s1`,`s2`,`rhs`,`lhs`]
        THEN SRW_TAC [] []);

val rtc_rderives_same_append_left = store_thm ("rtc_rderives_same_append_left",
``∀u v.RTC (rderives g) u v ⇒ ∀x. RTC (rderives g) (x++u) (x++v)``,
        HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
        METIS_TAC [RTC_RULES,rderives_same_append_left]);

val language_not_empty = store_thm ("language_not_empty",
``∀g.gaw g (NTS (startSym g))  ⇒ ~(language g = {})``,
SRW_TAC [] [] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [startSym, gaw, EXTENSION] THEN
SRW_TAC [] [language] THEN
METIS_TAC [startSym]);

val inNonTerminals = store_thm ("inNonTerminals",
``∀l r g.MEM (rule l r) (rules g) ⇒ (∀nt. (MEM (NTS nt) r) ⇒ (NTS nt) IN nonTerminals g)``,
SRW_TAC [] [] THEN
`∃r1 r2.r = r1++[NTS nt]++r2` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [] [slemma1_4] THEN
METIS_TAC [slemma1_4]);

val NTS_IN_rule_terminals = store_thm(
  "NTS_IN_rule_terminals",
  ``~(NTS N ∈ rule_terminals r)``,
  Cases_on `r` THEN SRW_TAC [][rule_terminals, isTmnlSym_def]);
val _ = export_rewrites ["NTS_IN_rule_terminals"]

val NTS_IN_terminals = store_thm(
  "NTS_IN_terminals",
  ``~(NTS N ∈ terminals g)``,
  Cases_on `g` THEN SPOSE_NOT_THEN ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [terminals] THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["NTS_IN_terminals"]

val gawAllSyms = store_thm ("gawAllSyms",
  ``∀e l. MEM e l ⇒ (l=SET_TO_LIST (allSyms g)) ⇒
          (∀nt. nt IN nonTerminals g ⇒
                ∃w. RTC (derives g) [nt] w ∧ EVERY isTmnlSym w) ⇒
          gaw g e``,
  SRW_TAC [][allSyms] THEN
  `(∃t. e = TS t) ∨ (∃N. e = NTS N)` by (Cases_on `e` THEN SRW_TAC [][]) THEN
  SRW_TAC [][] THEN1
    (SRW_TAC [][gaw] THEN Q.EXISTS_TAC `[TS t]` THEN
     SRW_TAC [][isTmnlSym_def]) THEN
  `FINITE (LIST_TO_SET (rules g))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
  `NTS N ∈ nonTerminals g ∨ NTS N ∈ terminals g`
     by METIS_TAC [SET_TO_LIST_IN_MEM, finiteAllSyms, allSyms, MEM,
                   IN_UNION]
  THENL [
    METIS_TAC [gaw],
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val ruleRhsInAllSyms = store_thm ("ruleRhsInAllSyms",
``∀lhs rhs.MEM (rule lhs rhs) (rules g) ⇒
(∀e.MEM e rhs ⇒ e IN (allSyms g))``,
SRW_TAC [] [allSyms] THEN
Cases_on `e` THEN
METIS_TAC [slemma1_4, slemma1_4Tmnls, rgr_r9eq]);



val rderivesHdTmnl = store_thm ("rderivesHdTmnl",
``rderives g u u' ⇒ isTmnlSym (HD u) ⇒ (HD u' = HD u)``,
SRW_TAC [] [rderives] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);

val derivesHdTmnl = store_thm ("derivesHdTmnl",
``derives g u u' ⇒ isTmnlSym (HD u) ⇒ (HD u' = HD u)``,
SRW_TAC [] [derives_def] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);

val rderivesNotNil = store_thm ("rderivesNotNil",
``∀l l' g.rderives g l l' ⇒ ~(l=[])``,
SRW_TAC [] [rderives] THEN
Cases_on `s1` THEN SRW_TAC [] []);


val rtcRderivesInRuleRhsLen = store_thm
("rtcRderivesInRuleRhsLen",
``∀u v.RTC (rderives g) u v ⇒
  (u=[NTS N]) ⇒ (LENGTH v > 1) ⇒ MEM sym v ⇒
(∃lhs rhs p s.MEM (rule lhs (p++[sym]++s)) (rules g))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
Cases_on `v` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [rderives],

      Cases_on `t` THEN SRW_TAC [] []
      THENL[
            FULL_SIMP_TAC (srw_ss()) [rderives, lreseq] THEN
            SRW_TAC [] [] THEN
            METIS_TAC [APPEND_NIL, rgr_r9eq],

            FULL_SIMP_TAC (srw_ss()) [] THEN
            FULL_SIMP_TAC (arith_ss) [] THEN
            FULL_SIMP_TAC (srw_ss()) [rderives] THEN
            Cases_on `s1` THEN Cases_on `s2` THEN
            SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
            METIS_TAC [rgr_r9eq, MEM_APPEND, APPEND, MEM]
            ]]);

val rtcDerivesInRuleRhsLen = store_thm
("rtcDerivesInRuleRhsLen",
``∀u v.RTC (derives g) u v ⇒
  (u=[NTS N]) ⇒ (LENGTH v > 1) ⇒ MEM sym v ⇒
(∃lhs rhs p s.MEM (rule lhs (p++[sym]++s)) (rules g))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
Cases_on `v` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def],

      Cases_on `t` THEN SRW_TAC [] []
      THENL[
            FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
            SRW_TAC [] [] THEN
            METIS_TAC [APPEND_NIL, rgr_r9eq],

            FULL_SIMP_TAC (srw_ss()) [] THEN
            FULL_SIMP_TAC (arith_ss) [] THEN
            FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
            Cases_on `s1` THEN Cases_on `s2` THEN
            SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
            METIS_TAC [rgr_r9eq, MEM_APPEND, APPEND, MEM]
            ]]);



val rtcDerivesInRuleRhsLenGte1 = store_thm
("rtcDerivesInRuleRhsLenGte1",
``∀u v.RTC (derives g) u v ⇒
  (u=[NTS N]) ⇒ (LENGTH v >= 1) ⇒ (u ≠ v) ⇒ MEM sym v ⇒
(∃lhs rhs p s.MEM (rule lhs (p++[sym]++s)) (rules g))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
Cases_on `v` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def],

      Cases_on `t` THEN SRW_TAC [] []
      THENL[
            FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
            SRW_TAC [] [] THEN
            METIS_TAC [APPEND_NIL, rgr_r9eq],

            FULL_SIMP_TAC (srw_ss()) [] THEN
            FULL_SIMP_TAC (arith_ss) [] THEN
            FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
            Cases_on `s1` THEN Cases_on `s2` THEN
            SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
            METIS_TAC [rgr_r9eq, MEM_APPEND, APPEND, MEM]
            ]]);


val rtcRderivesInRuleRhs =
store_thm ("rtcRderivesInRuleRhs",
   `` RTC (rderives g) [NTS N] (pfx ++ [sym] ++ sfx) ⇒
       ~(pfx = []) ∨ ~(sfx = []) ⇒
       ∃lhs rhs p s. MEM (rule lhs (p ++ [sym] ++ s)) (rules g)``,
SRW_TAC [] []
THENL[
      Cases_on `pfx` THEN SRW_TAC [] []THEN
      `LENGTH (h::t ++ [sym] ++ sfx) > 1` by (FULL_SIMP_TAC (srw_ss()) [] THEN
                                              FULL_SIMP_TAC (arith_ss) []) THEN
      METIS_TAC [rtcRderivesInRuleRhsLen, MEM_APPEND, MEM],

      Cases_on `sfx` THEN SRW_TAC [] []THEN
      `LENGTH (pfx ++ [sym] ++ h::t) > 1` by (FULL_SIMP_TAC (srw_ss()) [] THEN
                                              FULL_SIMP_TAC (arith_ss) []) THEN
      METIS_TAC [rtcRderivesInRuleRhsLen, MEM_APPEND, MEM]]);


val rtcDerivesInRuleRhs =
store_thm ("rtcDerivesInRuleRhs",
   `` RTC (derives g) [NTS N] (pfx ++ [sym] ++ sfx) ⇒
       ~(pfx = []) ∨ ~(sfx = []) ⇒
       ∃lhs rhs p s. MEM (rule lhs (p ++ [sym] ++ s)) (rules g)``,
SRW_TAC [] []
THENL[
      Cases_on `pfx` THEN SRW_TAC [] []THEN
      `LENGTH (h::t ++ [sym] ++ sfx) > 1` by (FULL_SIMP_TAC (srw_ss()) [] THEN
                                              FULL_SIMP_TAC (arith_ss) []) THEN
      METIS_TAC [rtcDerivesInRuleRhsLen, MEM_APPEND, MEM],

      Cases_on `sfx` THEN SRW_TAC [] []THEN
      `LENGTH (pfx ++ [sym] ++ h::t) > 1` by (FULL_SIMP_TAC (srw_ss()) [] THEN
                                              FULL_SIMP_TAC (arith_ss) []) THEN
      METIS_TAC [rtcDerivesInRuleRhsLen, MEM_APPEND, MEM]]);


val rtcDerivesInRuleRhs' =
store_thm ("rtcDerivesInRuleRhs'",
   `` RTC (derives g) [NTS N] (pfx ++ [sym] ++ sfx) ⇒
	   ([NTS N] ≠ (pfx++[sym]++sfx))
	   ⇒
	 ∃lhs rhs p s. MEM (rule lhs (p ++ [sym] ++ s)) (rules g)``,
SRW_TAC [] [] THEN
Cases_on `pfx=[]` THEN Cases_on `sfx=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(`LENGTH [sym] >= 1` by FULL_SIMP_TAC (arith_ss) [LENGTH] THEN
METIS_TAC [rtcDerivesInRuleRhsLenGte1, MEM]) THEN1
(`LENGTH (sym::sfx) >= 1` by FULL_SIMP_TAC (arith_ss) [LENGTH] THEN
`[NTS N] ≠ (sym::sfx)` by SRW_TAC [][] THEN
METIS_TAC [rtcDerivesInRuleRhsLenGte1, MEM, APPEND]) THEN1
(`LENGTH (pfx++[sym]) >= 1` by FULL_SIMP_TAC (arith_ss) [LENGTH, LENGTH_APPEND] THEN
`[NTS N] ≠ (pfx++[sym])` by SRW_TAC [][] THEN
METIS_TAC [rtcDerivesInRuleRhsLenGte1, MEM, MEM_APPEND]) THEN
`LENGTH (pfx++[sym]++sfx) >= 1`
	   by FULL_SIMP_TAC (arith_ss) [LENGTH, LENGTH_APPEND] THEN
`[NTS N] ≠ (pfx++[sym]++sfx)` by SRW_TAC [][] THEN
METIS_TAC [rtcDerivesInRuleRhsLenGte1, MEM, MEM_APPEND]);



val infiniteSyms = store_thm
("infiniteSyms",
``INFINITE (UNIV:'a set)  ⇒ INFINITE (UNIV:('a,'b) symbol set)``,

STRIP_TAC THEN
`∀x y.(NTS x = NTS y) ⇒ (x=y)`  by SRW_TAC [][] THEN
IMP_RES_TAC IMAGE_11_INFINITE THEN
POP_ASSUM (MATCH_MP_TAC o MATCH_MP INFINITE_SUBSET) THEN
SRW_TAC [][]);

val ldres1 = store_thm
("ldres1",
``∀lhs rhs g.
         MEM (rule lhs rhs) (rules g)
	     ⇒
	     lderives g [NTS lhs] rhs``,
	     SRW_TAC [] [lderives]
	     THEN MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`]
 THEN SRW_TAC [] []);

 val listPairExistsD = store_thm
("listPairExistsD",
``∀x y.derives g x y
   ⇒
  ∃l.(x=MAP FST l) ∧ (y = FLAT (MAP SND l)) ∧
  (∀a b.MEM (a,b) l ⇒ ∃dl'.LENGTH dl' ≤ 2 ∧
                      (derives g) ⊢ dl' ◁ [a] → b)``,

SRW_TAC [][derives_def] THEN
`∃l1.(s1=MAP FST l1) ∧ (s1= FLAT (MAP SND l1)) ∧
  (∀a b.MEM (a,b) l1 ⇒  (LENGTH b = 1) ∧ (a=HD b))`
by METIS_TAC [listPairExists] THEN
`∃l2.(s2=MAP FST l2) ∧ (s2= FLAT (MAP SND l2)) ∧
  (∀a b.MEM (a,b) l2 ⇒  (LENGTH b = 1) ∧ (a=HD b))`
by METIS_TAC [listPairExists] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `l1++[(NTS lhs,rhs)]++l2` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [FLAT_APPEND]
THENL[
      RES_TAC THEN
      SRW_TAC [][] THEN
      Cases_on `b` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `t=[]` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `[[h]]` THEN
      SRW_TAC [][listderiv_def],


      Q.EXISTS_TAC `[[NTS lhs];b]` THEN
      SRW_TAC [][listderiv_def,derives_def] THEN
      METIS_TAC [APPEND_NIL],

      RES_TAC THEN
      SRW_TAC [][] THEN
      Cases_on `b` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `t=[]` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `[[h]]` THEN
      SRW_TAC [][listderiv_def]
      ]);


val listPairExistsLd = store_thm
("listPairExistsLd",
``∀x y.(derives g) ⊢ dl ◁ x → y
   ⇒
  ∃l.(x=MAP FST l) ∧ (y = FLAT (MAP SND l)) ∧
  (∀a b.MEM (a,b) l ⇒ ∃dl'.LENGTH dl' ≤ LENGTH dl ∧
                      (derives g) ⊢ dl' ◁ [a] → b)``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(`∃l'.(h=MAP FST l') ∧ (h= FLAT (MAP SND l')) ∧
  (∀a b.MEM (a,b) l' ⇒  (LENGTH b = 1) ∧ (a=HD b))`
by METIS_TAC [listPairExists] THEN
Q.EXISTS_TAC `l'` THEN SRW_TAC [][] THEN
RES_TAC THEN
SRW_TAC [][] THEN
Cases_on `b` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`t=[]` by METIS_TAC [LENGTH_NIL] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `[[h]]` THEN
SRW_TAC [][listderiv_def]) THEN

`t=FRONT t ++ [LAST t]` by METIS_TAC [APPEND_FRONT_LAST] THEN
Cases_on `FRONT t = []` THEN SRW_TAC [][] THEN1
(`derives g h (LAST t)` by METIS_TAC [rtc2list_def,APPEND_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
SRW_TAC [][] THEN
`derives g (s1 ++ [NTS lhs] ++ s2) (s1++rhs++s2)` by METIS_TAC [rtc2list_def] THEN
IMP_RES_TAC listPairExistsD THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `l` THEN
SRW_TAC [][] THEN1
METIS_TAC [last_append,APPEND] THEN
RES_TAC THEN
 `LENGTH dl' ≤ SUC (LENGTH [LAST t])` by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
METIS_TAC [listderiv_def]) THEN
`LENGTH (h::FRONT t) < SUC (LENGTH t) ` by
(FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 METIS_TAC [frontLen]) THEN
`rtc2list (derives g) (h::FRONT t)`
by METIS_TAC [rtc2list_distrib_append_fst,APPEND_ASSOC,NOT_CONS_NIL,APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH (h::FRONT t)`] MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h::FRONT t`] MP_TAC) THEN
SRW_TAC [][] THEN
`rtc2list (derives g) ([MAP FST l]++(FRONT (FRONT t)) ++
[LAST (FRONT t)]++[LAST t])` by
METIS_TAC [APPEND,APPEND_ASSOC,APPEND_FRONT_LAST] THEN
`rtc2list (derives g) ([(LAST (FRONT t))]++[(LAST t)])`
by METIS_TAC [rtc2list_distrib_append_snd,APPEND_ASSOC,MEM,MEM_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
`FLAT (MAP SND l) = s1 ++ [NTS lhs] ++ s2 ` by METIS_TAC [last_append,
APPEND] THEN
IMP_RES_TAC flatMem THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `TAKE (LENGTH p) l ++
[(FST (HD (DROP (LENGTH p) l)),p' ++ rhs ++ s')] ++
DROP (1+LENGTH p) l` THEN
SRW_TAC [][]
THENL[

Cases_on `l=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [mapFstEq],

IMP_RES_TAC mapSndTakeEq THEN
IMP_RES_TAC mapSndDropEq THEN
SRW_TAC [][FLAT_APPEND] THEN
METIS_TAC [APPEND,last_append,APPEND_ASSOC],


`LENGTH p ≤ LENGTH l` by
(`LENGTH l = LENGTH (p ++ [p' ++ [NTS lhs] ++ s'] ++ s)`
 by METIS_TAC [LENGTH_MAP] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`SUC (LENGTH (FRONT t)) ≤ SUC (LENGTH t)` by
(`LENGTH (FRONT t) < LENGTH t` by METIS_TAC [frontLen] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`MEM (a,b) l` by METIS_TAC [IS_EL_FIRSTN] THEN
RES_TAC THEN
`LENGTH dl' ≤ SUC(LENGTH t)`  by DECIDE_TAC THEN
METIS_TAC [],


`LENGTH p < LENGTH l` by
(`LENGTH l = LENGTH (p ++ [p' ++ [NTS lhs] ++ s'] ++ s)` by METIS_TAC [LENGTH_MAP] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`LENGTH p ≤ LENGTH l` by
(`LENGTH l = LENGTH (p ++ [p' ++ [NTS lhs] ++ s'] ++ s)` by METIS_TAC [LENGTH_MAP] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`DROP (LENGTH p) (MAP SND l) = [p' ++ [NTS lhs] ++ s'] ++ s` by
METIS_TAC [dropLen,APPEND_ASSOC,LENGTH_MAP] THEN
`LENGTH (DROP (LENGTH p) l)  = LENGTH (DROP (LENGTH p) (MAP SND l))`
by METIS_TAC [mapDrop,LENGTH_MAP] THEN
`∃f.HD (DROP (LENGTH p) l) = (f,p' ++ [NTS lhs] ++ s')` by
(`LENGTH l = LENGTH (MAP SND l)` by METIS_TAC [LENGTH_MAP] THEN
`LENGTH (DROP (LENGTH p) (MAP SND l)) = LENGTH ([p' ++ [NTS lhs] ++ s'] ++ s)`
by METIS_TAC [] THEN
Cases_on `DROP (LENGTH p) l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`MAP SND (DROP (LENGTH p) l) = MAP SND ((q,r)::t')`by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [mapDrop]) THEN
Cases_on `DROP (LENGTH p) l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [dropNotNil] THEN
SRW_TAC [][] THEN
`MEM (f,p' ++ [NTS lhs] ++ s') l` by METIS_TAC [IS_EL_BUTFIRSTN,MEM] THEN
RES_TAC THEN
`SUC (LENGTH (FRONT t)) ≤ SUC (LENGTH t)` by
(`LENGTH (FRONT t) < LENGTH t` by METIS_TAC [frontLen] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`SUC (LENGTH dl') ≤ SUC(LENGTH t)`  by DECIDE_TAC THEN
Q.EXISTS_TAC `dl'++[p'++rhs++s']` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (arith_ss) []
THENL[
`derives g (LAST dl') (p'++rhs++s')` by METIS_TAC [derives_def,APPEND_NIL] THEN
METIS_TAC [rtc2list_append_right],

Cases_on` dl'` THEN FULL_SIMP_TAC (srw_ss()) []
],


`1+LENGTH p ≤ LENGTH l` by
(`LENGTH l = LENGTH (p ++ [p' ++ [NTS lhs] ++ s'] ++ s)` by METIS_TAC [LENGTH_MAP] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`MEM (a,b) l` by METIS_TAC [IS_EL_BUTFIRSTN] THEN
RES_TAC THEN
`LENGTH dl' ≤ SUC(LENGTH t)`  by DECIDE_TAC THEN
METIS_TAC []]);


val ldStartTs = store_thm
("ldStartTs",
``∀dl ts syms y.(derives g) ⊢ dl ◁ (TS ts::syms) → y
	⇒
   ∃rst dl'. (y=TS ts::rst) ∧ LENGTH dl' ≤ LENGTH dl ∧
             (derives g) ⊢ dl' ◁ syms → rst``,

Induct_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(Q.EXISTS_TAC `[syms]` THEN
SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `(t'++[NTS lhs]++s2)::dl'` THEN
SRW_TAC [][] THEN1
METIS_TAC [rtc2list_def,last_append,APPEND] THEN
Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][derives_def] THEN
METIS_TAC [APPEND_NIL]);

val firstNt_in_block1 = prove(
  ``∀m s1. (m ++ s = s1 ++ [NTS N] ++ s2) ∧ isWord s1 ∧
           EXISTS ($~ o isTmnlSym) m ⇒
           ∃s0. (m = s1 ++ [NTS N] ++ s0) ∧ (s2 = s0 ++ s)``,
  Induct_on `m` THEN SRW_TAC [][] THEN
  Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);

val firstNt = prove(
  ``∀l. EXISTS ($~ o isTmnlSym) l ⇒
        ∃pfx sfx nt. (l = pfx ++ [NTS nt] ++ sfx) ∧ isWord pfx``,
  Induct THEN SRW_TAC [][] THENL [
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
    Q.EXISTS_TAC `[]` THEN SRW_TAC [][],
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      Q.EXISTS_TAC `[]` THEN SRW_TAC [][],
      Q.EXISTS_TAC `TS t::pfx` THEN
      SRW_TAC [][isTmnlSym_def] THEN METIS_TAC []
    ]
  ]);

val firstNt_in_block2 = prove(
  ``∀p s1. (p ++ m ++ s = s1 ++ [NTS N] ++ s2) ∧
           isWord p ∧ isWord s1 ∧ EXISTS ($~ o isTmnlSym) m ⇒
           ∃p' s0. (s1 = p ++ p') ∧ (s2 = s0 ++ s) ∧
                   (m = p' ++ [NTS N] ++ s0)``,
  Induct_on `p` THEN SRW_TAC [][] THEN1 METIS_TAC [firstNt_in_block1] THEN
  `(s1 = []) ∨ ∃s0 ss. s1 = s0::ss` by (Cases_on `s1` THEN SRW_TAC [][])
  THENL [
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val LAST_CONS_NOT_NIL = prove(
  ``t ≠ [] ⇒ (LAST (h::t) = LAST t)``,
  Cases_on `t` THEN SRW_TAC [][]);

val rtc2listldFstNt0 = prove(
  ``∀sfx m.
      rtc2list (lderives g) ((p ++ m ++ rst)::sfx) ∧ ¬isWord m ∧
      isWord p ∧ sfx ≠ [] ∧ isWord (LAST sfx) ⇒
      ∃r1 r2 tl. (sfx = r1 ++ [p ++ tl ++ rst] ++ r2) ∧ isWord tl ∧
                 ∀e. MEM e r1 ⇒
                     ∃p0 p1 nt. (e = p ++ p0 ++ [NTS nt] ++ p1 ++ rst) ∧
                                isWord p0``,
  Induct THEN1 SRW_TAC [][] THEN SRW_TAC [][rtc2list_def] THEN
  `∃s1 s2 rhs N. (p ++ m ++ rst = s1 ++ [NTS N] ++ s2) ∧
                 isWord s1 ∧ (h = s1 ++ rhs ++ s2) ∧
                 MEM (rule N rhs) (rules g)`
     by METIS_TAC [lderives] THEN
  `∃p' rst0. (s1 = p ++ p') ∧ (s2 = rst0 ++ rst) ∧ (m = p' ++ [NTS N] ++ rst0)`
     by METIS_TAC [firstNt_in_block2] THEN
  SRW_TAC [][] THEN Q.PAT_ASSUM `EXISTS PP l` (K ALL_TAC) THEN
  Cases_on `isWord (rhs ++ rst0)` THEN1
    (MAP_EVERY Q.EXISTS_TAC [`[]`, `sfx`, `p' ++ rhs ++ rst0`] THEN
     FULL_SIMP_TAC (srw_ss()) []) THEN
  `sfx ≠ []` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
                 METIS_TAC [NOT_EVERY]) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `p' ++ rhs ++ rst0` MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `isWord rhs` THEN
  FULL_SIMP_TAC (srw_ss()) [LAST_CONS_NOT_NIL] THEN1
    METIS_TAC [NOT_EVERY] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`(p ++ p' ++ rhs ++ rst0 ++ rst) :: r1`,
                          `r2`, `tl`] THEN
  SRW_TAC [][] THENL [
    SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11] THEN
    `∃rst_p rst_N rst_s. (rst0 = rst_p ++ [NTS rst_N] ++ rst_s) ∧
                         isWord rst_p`
       by METIS_TAC [firstNt] THEN
    Q.EXISTS_TAC `p' ++ rhs ++ rst_p` THEN
    ASM_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11, APPEND] THEN
    SRW_TAC [][],
    METIS_TAC [],

    `∃rhs_p rhs_N rhs_s. (rhs = rhs_p ++ [NTS rhs_N] ++ rhs_s) ∧
                         isWord rhs_p`
       by METIS_TAC [firstNt] THEN
    Q.EXISTS_TAC `p' ++ rhs_p` THEN
    ASM_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11] THEN
    SRW_TAC [][],
    METIS_TAC []
  ]);

val rtc2listldFstNt' = store_thm
("rtc2listldFstNt'",
``∀pfx sfx.
    rtc2list (lderives g) l ∧
    (l = pfx++[p++m++rst]++sfx) ∧ ¬(EVERY isTmnlSym m) ∧
    EVERY isTmnlSym p ∧ EVERY isTmnlSym (LAST l) ⇒
    ∃r1 r2 tl.(sfx = r1 ++ [p++tl++rst] ++ r2)  ∧ EVERY isTmnlSym tl ∧
    (∀e.MEM e r1 ⇒
     ∃p0 p1 nt.(e = p ++ p0 ++ [NTS nt] ++ p1 ++ rst) ∧ isWord p0)``,
REPEAT STRIP_TAC THEN
`rtc2list (lderives g) ((p ++ m ++ rst)::sfx)`
    by METIS_TAC [rtc2list_distrib_append_snd, NOT_NIL_CONS, APPEND,
                  APPEND_ASSOC] THEN
`sfx ≠ []` by (STRIP_TAC THEN SRW_TAC [][] THEN
               FULL_SIMP_TAC (srw_ss()) [LAST_APPEND] THEN
               METIS_TAC [NOT_EVERY]) THEN
`LAST l = LAST sfx`
   by ASM_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND, LAST_APPEND,
                            LAST_CONS_NOT_NIL] THEN
`∃r1 r2 tl. (sfx = r1 ++ [p ++ tl ++ rst] ++ r2) ∧ isWord tl ∧
            ∀e. MEM e r1 ⇒
                ∃p0 p1 nt. (e = p ++ p0 ++ [NTS nt] ++ p1 ++ rst) ∧
                           isWord p0`
   by (MATCH_MP_TAC rtc2listldFstNt0 THEN METIS_TAC []) THEN
METIS_TAC []);

val lderivesPfxSame = store_thm
("lderivesPfxSame",
``∀dl s1 rst.
    (lderives g) ⊢ dl ◁ (s1++rst) → v  ∧ EVERY isTmnlSym s1
    ⇒
    ∀e.MEM e dl ⇒ ∃sfx.(s1++sfx = e)``,

Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
(FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN
IMP_RES_TAC list_r6 THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]));


val lderivesRtc2listPfxSame = store_thm
("lderivesRtc2listPfxSame",
``∀rst t.rtc2list (lderives g) ((h++rst)::t) ∧ EVERY isTmnlSym h
 ⇒
 ∀e.MEM e t ⇒ ∃sfx.(h++sfx=e)``,

Induct_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN
 (IMP_RES_TAC list_r6 THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
  METIS_TAC [APPEND_ASSOC]));


val listsecAddFront = store_thm
("listsecAddFront",
``∀l.(MAP (listsec v []) (MAP (addFront v) l) = l)``,

Induct_on `l` THEN SRW_TAC [][listsec_def, dropLast_def,addFront_def] THEN
METIS_TAC [BUTFIRSTN_LENGTH_APPEND]);


val maplistsecAddfront = store_thm
("maplistsecAddfront",
``∀t.(∀e.MEM e t ⇒ ∃rst.(e=v++rst)) ⇒
((MAP (listsec v []) t = l) ⇔ (t = MAP (addFront v) l))``,

Induct_on `t` THEN SRW_TAC [][listsec_def] THEN
FULL_SIMP_TAC (srw_ss()) [dropLast_def] THEN1
METIS_TAC [] THEN
SRW_TAC [][EQ_IMP_THM] THEN
`∃rst.h=v ++ rst` by METIS_TAC [] THEN
SRW_TAC [][addFront_def] THEN1
METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND, addFrontListsec] THEN1
METIS_TAC [BUTFIRSTN_LENGTH_APPEND, APPEND, addFrontListsec] THEN
SRW_TAC [][BUTFIRSTN_LENGTH_APPEND] THEN
`MAP (listsec v ([]:β list)) ((v ++ rst)::t) =
MAP (listsec v ([]:β list)) (MAP (addFront v) l)`
by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [listsec_def,dropLast_def,BUTFIRSTN_LENGTH_APPEND] THEN
METIS_TAC [listsecAddFront]);



val ldAllTmnls = store_thm
("ldAllTmnls",
``lderives g ⊢ h::t ◁ x → y ∧ EVERY isTmnlSym x
 ⇒
(t=[])``,

SRW_TAC [][listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);


val rtc2listRtcldTmnls = store_thm
("rtc2listRtcldTmnls",
``∀t.rtc2list (lderives g) (h::t) ∧ EVERY isTmnlSym h
 ⇒
(t=[])``,


SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);

val listderivTrans = store_thm
("listderivTrans",
 ``∀dl1 dl2 x y. R ⊢ dl1 ◁ x → y ∧ R ⊢ dl2 ◁ y → z ⇒
                 R ⊢ dl1 ++ TL dl2 ◁ x → z``,

Induct_on `dl1` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `dl2` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl1=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'::t`] MP_TAC) THEN SRW_TAC [][] THEN
Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) []);

val listsec_nil2 = prove(
  ``listsec v [] = DROP (LENGTH v)``,
  SRW_TAC [][listsec_def, FUN_EQ_THM, dropLast_def]);

val symRepProp_rwts = prove(
  ``(symRepProp [] = F) ∧
    (symRepProp [x] = F)``,
  SRW_TAC [][symRepProp_def, APPEND_EQ_SING] THEN
  Cases_on `s = []` THEN SRW_TAC [][]);

val listeq_wNs_ws = prove(
  ``(s1 ++ [NTS N] ++ s2 = w ++ rst) ∧
    isWord w ∧ isWord s1 ⇒
    ∃s1'. (s1 = w ++ s1') ∧ (rst = s1' ++ [NTS N] ++ s2)``,
  Q.ID_SPEC_TAC `w` THEN Induct_on `s1` THEN SRW_TAC [][] THENL [
    Cases_on `w` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
    Cases_on `w` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
    Cases_on `w` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
  ]);


val notspropLsTmnls = store_thm
("notspropLsTmnls",
``∀dl v rst.
   ¬symRepProp dl ∧ lderives g ⊢ dl ◁ (v ++ rst) → (v ++ rst') ∧
   EVERY isTmnlSym (v++rst') ⇒
   ¬symRepProp (MAP (listsec v []) dl)``,
SIMP_TAC (srw_ss()) [listsec_nil2] THEN
Induct_on `dl` THEN SRW_TAC [][] THEN
`¬symRepProp dl` by METIS_TAC [TL, NOT_CONS_NIL, spropApp] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [symRepProp_rwts] THEN
IMP_RES_TAC listDerivHdBrk THEN
`h = v ++ rst` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][BUTFIRSTN_LENGTH_APPEND] THEN
`∃rst1. h' = v ++ rst1`
   by (FULL_SIMP_TAC (srw_ss()) [lderives] THEN
       `∃s1'. (s1 = v ++ s1') ∧ (rst = s1' ++ [NTS lhs] ++ s2)`
          by METIS_TAC [listeq_wNs_ws] THEN
       SRW_TAC [][] THEN SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11]) THEN
SRW_TAC [][BUTFIRSTN_LENGTH_APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`v`,`rst1`] MP_TAC) THEN
SRW_TAC [][BUTFIRSTN_LENGTH_APPEND] THEN
DISCH_THEN (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [symRepProp_def]) THEN
Q.PAT_ASSUM `¬symRepProp ((v++rst) :: R)` MP_TAC THEN SRW_TAC [][] THEN
SRW_TAC [][symRepProp_def] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (APPEND v) p`, `v ++ tsl`, `B`, `sfx`, `v'`,
                        `w`] THEN
ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (APPEND v) s0`, `MAP (APPEND v) s1`] THEN
SRW_TAC [][MEM_MAP] THENL [
  Q_TAC (fn t => FIRST_X_ASSUM (MP_TAC o AP_TERM t)) `MAP (APPEND v)` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q_TAC SUFF_TAC `MAP (APPEND v) (MAP (DROP (LENGTH v)) t) = t` THEN1
  SRW_TAC [][] THEN
  Q.PAT_ASSUM `lderives g ⊢ dl ◁ X → Y` MP_TAC THEN
  Q.UNDISCH_THEN `isWord v` MP_TAC THEN
  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
  Q.ID_SPEC_TAC `rst1` THEN Induct_on `t` THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN
  IMP_RES_TAC listDerivHdBrk THEN
  `∃rst. h = v ++ rst`
     by (FULL_SIMP_TAC (srw_ss()) [lderives] THEN
         `∃s1'. (s1 = v ++ s1') ∧ (rst1 = s1' ++ [NTS lhs] ++ s2)`
             by METIS_TAC [listeq_wNs_ws] THEN
         REPEAT BasicProvers.VAR_EQ_TAC THEN
         SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11]) THEN
  SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss()) [BUTFIRSTN_LENGTH_APPEND] THEN
  METIS_TAC [],

  SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND_11] THEN
  SRW_TAC [][]
]);

val ntList = Define
`ntList g = nonTerminalsList (startSym g) (rules g)`;

val ntms = Define
    `ntms g = rmDupes (ntList g)`;

val rtcDReplEnd = store_thm
("rtcDReplEnd",
 ``∀i.(derives g)^* [NTS B] (p ++ [NTS B] ++ s) ∧
 (derives g)^*  [NTS B] z ∧ EVERY isTmnlSym z ∧
 (derives g)^* s z' ∧ EVERY isTmnlSym z'
  ⇒
  (derives g)^* [NTS B] (FLAT (lpow p i) ++ z ++ FLAT (lpow z' i))``,

Induct_on `i` THEN SRW_TAC [][] THEN1
(SRW_TAC [][lpow_def,REPLICATE] THEN
 METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	    APPEND_ASSOC,RTC_RTC]) THEN
RES_TAC THEN
SRW_TAC [][flatRepSuc] THEN
Q_TAC SUFF_TAC
`(derives g)^* [NTS B] (p ++ FLAT (lpow p i) ++ z ++  FLAT (lpow z' i) ++z')` THEN1
METIS_TAC [flatRepComm,APPEND_ASSOC] THEN
`(derives g)^* (p++[NTS B]++s) (p++FLAT (lpow p i) ++ z ++ FLAT (lpow z' i)++s)` by
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	   APPEND_ASSOC] THEN
METIS_TAC [RTC_RTC,rtc_derives_same_append_left]);

val rtcDReplEnd = store_thm
("rtcDReplEnd",
 ``∀i.(derives g)^* [NTS B] (p ++ [NTS B] ++ s) ∧
 (derives g)^*  [NTS B] z ∧ EVERY isTmnlSym z ∧
 (derives g)^* s z' ∧ EVERY isTmnlSym z'
  ⇒
  (derives g)^* [NTS B] (FLAT (lpow p i) ++ z ++ FLAT (lpow z' i))``,

Induct_on `i` THEN SRW_TAC [][] THEN1
(SRW_TAC [][lpow_def,REPLICATE] THEN
 METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	    APPEND_ASSOC,RTC_RTC]) THEN
RES_TAC THEN
SRW_TAC [][flatRepSuc] THEN
Q_TAC SUFF_TAC
`(derives g)^* [NTS B] (p ++ FLAT (lpow p i) ++ z ++  FLAT (lpow z' i) ++z')` THEN1
METIS_TAC [flatRepComm,APPEND_ASSOC] THEN
`(derives g)^* (p++[NTS B]++s) (p++FLAT (lpow p i) ++ z ++ FLAT (lpow z' i)++s)` by
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	   APPEND_ASSOC] THEN
METIS_TAC [RTC_RTC,rtc_derives_same_append_left]);


val nonTmnlsApp = store_thm
("nonTmnlsApp",
``∀l1 l2.nonTmnls (l1 ++ l2) = nonTmnls l1 ++ nonTmnls l2``,
Induct_on `l1` THEN SRW_TAC [][nonTmnls] THEN
Cases_on `h` THEN SRW_TAC [][nonTmnls]);

val ruleRhsInntms = store_thm
("ruleRhsInntms",
``∀rhs.MEM (rule lhs rhs) (rules g) ⇒
(MEM lhs (ntms g)) ∧
(∀e. MEM e rhs ∧ isNonTmnlSym e ⇒ ∃nt. (e = NTS nt) ∧ MEM nt (ntms g))``,

SRW_TAC [][rgr_r9eq] THEN
SRW_TAC [][ntms, ntList, nonTerminalsList, nonTmnlsApp, nonTmnls] THEN1
METIS_TAC [rmd_r2, rgr_r9eq, APPEND , APPEND_ASSOC] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
SRW_TAC [][FILTER_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, nts2str_def] THEN
METIS_TAC [rmd_r2, rgr_r9eq, APPEND , APPEND_ASSOC]);

val cardLenLeq = store_thm
("cardLenLeq",
``∀l.CARD (set s) ≤ LENGTH l ∧ (∀e.MEM e s ⇒ MEM e l) ∧ MEM x l ∧ ¬MEM x s
⇒
CARD ((set s) ∪ {x}) ≤ LENGTH l``,

SRW_TAC [][] THEN
`set s ⊂ set l` by
(SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [PSUBSET_DEF, EXTENSION, SUBSET_DEF] THEN
 METIS_TAC []) THEN
`CARD (set s) < CARD (set l)` by METIS_TAC [FINITE_LIST_TO_SET, CARD_PSUBSET] THEN
`CARD (set s ∪ {x}) ≤ CARD (set l)` by
(`set s ∪ {x} = x INSERT set s` by METIS_TAC [FINITE_LIST_TO_SET, INSERT_SING_UNION,
					      UNION_COMM] THEN
 SRW_TAC [][] THEN
 METIS_TAC [CARD_LIST_TO_SET,DECIDE ``a < b ⇒ SUC a ≤ b``]) THEN
METIS_TAC [CARD_LIST_TO_SET,DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``]);

val ldInTmnsApp = store_thm
("ldInTmnsApp",
``∀dl x.lderives g ⊢ dl ◁ x → y ∧
 (∀e.MEM e x ∧ isNonTmnlSym e ⇒ ∃nt.(e=NTS nt) ∧ MEM nt (ntms g)) ⇒
(∀e.MEM e (FLAT dl) ∧ isNonTmnlSym e ⇒ ∃nt.(e=NTS nt) ∧ MEM nt (ntms g))``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][]) THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC listDerivHdBrk THEN
FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN
`MEM lhs (ntms g) ∧
(∀e.MEM e rhs ∧ isNonTmnlSym e ⇒ ∃nt. (e = NTS nt) ∧ MEM nt (ntms g))`
by METIS_TAC [ruleRhsInntms] THEN1
METIS_TAC [MEM_APPEND, MEM] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs++s2`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);

val CARD_IMAGE = prove(
  ``∀s. FINITE s ⇒ (∀x y. (f x = f y) = (x = y)) ⇒
        (CARD (IMAGE f s) = CARD s)``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][]);

val FORALL_sym = prove(
  ``(∀e. P e) = (∀n. P (NTS n)) ∧ (∀t. P (TS t))``,
  SRW_TAC [][EQ_IMP_THM] THEN Cases_on `e` THEN SRW_TAC [][]);

val dldntsLeg = store_thm
("dldntsLeg",
``∀g dl x.lderives g ⊢ dl ◁ x → y ∧
 (∀e.MEM e x ∧ isNonTmnlSym e ⇒ ∃nt.(e=NTS nt) ∧ MEM nt (ntms g)) ⇒
LENGTH (distinctldNts dl) ≤ LENGTH (ntms g)``,

SIMP_TAC (srw_ss()) [LENGTH_distinctldNts, ntms, rmDupes_lts_card,
                     rmd_mem_list, GSYM rmDupes_lts] THEN
Q_TAC SUFF_TAC `
  ∀g dl x. lderives g ⊢ dl ◁ x → y ∧
           (∀e. MEM e x ∧ isNonTmnlSym e ⇒
                ∃nt. (e = NTS nt) ∧ MEM nt (ntList g)) ⇒
           set (ldNts dl) ⊆ IMAGE NTS (set (ntList g))
` THEN1 (REPEAT STRIP_TAC THEN
         `CARD (set (ntList g)) =
          CARD (IMAGE (NTS: 'a -> ('a,'b) symbol) (set (ntList g)))`
            by SRW_TAC [][CARD_IMAGE] THEN
         POP_ASSUM SUBST1_TAC THEN
         (CARD_SUBSET |> SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss)
                                   [AND_IMP_INTRO]
                      |> MATCH_MP_TAC) THEN
         SRW_TAC [][] THEN METIS_TAC []) THEN
SIMP_TAC (srw_ss()) [SUBSET_DEF, ldNts_def, MEM_FILTER, FORALL_sym,
                     isNonTmnlSym_def] THEN
Induct_on `dl` THEN1 SRW_TAC [][listderiv_def] THEN
SRW_TAC [][] THEN1
  (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN METIS_TAC []) THEN
`(dl = []) ∨ ∃sf sfs. dl = sf::sfs` by (Cases_on `dl` THEN SRW_TAC [][]) THEN1
FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPEC_THEN `g`
                           (MATCH_MP_TAC o SIMP_RULE (srw_ss() ++
                                                            boolSimps.DNF_ss)
                                                     [AND_IMP_INTRO])) THEN
SRW_TAC [][] THEN Q.EXISTS_TAC `sf` THEN
Q.PAT_ASSUM `MEM (NTS n) (FLAT XX)` (K ALL_TAC) THEN
IMP_RES_TAC listDerivHdBrk THEN SRW_TAC [][] THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][ntList, nonTerminalsList] THEN DISJ2_TAC THEN
Q_TAC SUFF_TAC `
  ∀list. MEM (rule lhs rhs) list ∧ MEM (NTS n) rhs ⇒ MEM n (nonTmnls list)
` THEN1 METIS_TAC [] THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Induct THEN SRW_TAC [][] THENL [
  SRW_TAC [][nonTmnls, MEM_MAP, MEM_FILTER] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC `NTS n` THEN
  SRW_TAC [][nts2str_def, isNonTmnlSym_def],
  Cases_on `h` THEN SRW_TAC [][nonTmnls]
]);


val symMemProp = store_thm
("symMemProp",
``∀dl x.lderives g ⊢ dl ◁ x → y ∧ EVERY isTmnlSym y ⇒
(LENGTH dl = 1) ∨ (∀e.MEM e (FRONT dl) ⇒ ∃p0 p1 nt.(e = p0++[NTS nt]++p1) ∧
		   EVERY isTmnlSym p0)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC listDerivHdBrk THEN
`x = h` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'`] MP_TAC) THEN SRW_TAC [][] THEN1

(`t=[]` by METIS_TAC [LENGTH_NIL] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [lderives, listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_NIL]) THEN1

(FULL_SIMP_TAC (srw_ss()) [lderives] THEN
 SRW_TAC [][] THEN
 METIS_TAC []) THEN1

(`t=[]` by METIS_TAC [LENGTH_NIL] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [lderives, listderiv_def] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_NIL]) THEN

(FULL_SIMP_TAC (srw_ss()) [lderives] THEN
 SRW_TAC [][] THEN
 METIS_TAC []));

val symPropExists = store_thm
("symPropExists",
``lderives g ⊢ dl ◁ x → z ∧
(dl = ([[NTS A]] ++ p ++ [p0 ++ [NTS A] ++ s0] ++ s)) ∧
  EVERY isTmnlSym z ⇒
  symRepProp dl``,

 SRW_TAC [][] THEN
 IMP_RES_TAC symMemProp THEN
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 `s ≠ []` by
 (SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  `EVERY isTmnlSym (p0 ++ [NTS A] ++ s0)` by METIS_TAC [last_elem, APPEND] THEN
  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
 `s = FRONT s ++ [LAST s]` by METIS_TAC [APPEND_FRONT_LAST] THEN
 SRW_TAC [][] THEN
`(FRONT ([NTS A]::(p ++ [p0 ++ [NTS A] ++ s0] ++ s)) = [NTS A]::
  (p ++ [p0 ++ [NTS A] ++ s0] ++ FRONT s))` by METIS_TAC [frontAppendFst, APPEND,
							  APPEND_ASSOC] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
Cases_on `EVERY isTmnlSym p0`
THENL[
      FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`[]`,`A`,`[]`,`p0`,`s0`,
				   `(p ++ [p0 ++ [NTS A] ++ s0] ++ s)`] MP_TAC) THEN
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`p`,`s`] THEN
      SRW_TAC [][] THEN
      METIS_TAC [everyNotTwice],

      IMP_RES_TAC leftnt THEN
      SRW_TAC [][] THEN
      `rtc2list (lderives g) ([NTS A]::
			      (p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++ s))`
      by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `¬EVERY isTmnlSym ([NTS n]++l2)` by SRW_TAC [][isTmnlSym_def] THEN
      `EVERY isTmnlSym (LAST ([NTS A]::
			      (p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++ s)))`
      by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `([NTS A]::(p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++ s) =
       ([NTS A]::p) ++ [l1 ++ ([NTS n] ++ l2) ++ ([NTS A] ++ s0)] ++ s)`
      by METIS_TAC [APPEND_ASSOC, APPEND] THEN
      `∀tl.l1 ++ tl ++ [NTS A] ++ s0 = l1 ++ tl ++ ([NTS A] ++ s0)`
      by METIS_TAC [APPEND_ASSOC] THEN
      `∃r1 r2 tl. (s = r1 ++ [l1 ++ tl ++ [NTS A] ++ s0] ++ r2) ∧ isWord tl `
      by METIS_TAC [rtc2listldFstNt'] THEN
      SRW_TAC [][] THEN
      `(LENGTH ([NTS A]::
                 (p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++
                  (r1 ++ [l1 ++ tl ++ [NTS A] ++ s0] ++ r2))) = 1) ∨
        ∀e.MEM e ([NTS A]::
              (p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++
               FRONT (r1 ++ [l1 ++ tl ++ [NTS A] ++ s0] ++ r2))) ⇒
      ∃p0 p1 nt.(e = p0 ++ [NTS nt] ++ p1)`
      by METIS_TAC [symMemProp] THEN
      FULL_SIMP_TAC (srw_ss()++ARITH_ss) [symRepProp_def] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`[]`,`A`,`[]`,`l1++tl`,`s0`,
				   `(p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++
				     r1 ++ [l1 ++ tl ++ [NTS A] ++ s0] ++ r2)`]
		     MP_TAC) THEN SRW_TAC [][] THEN1
      METIS_TAC [APPEND_ASSOC, APPEND_NIL, everyNotTwice, EVERY_DEF, NOT_EVERY] THEN1

      METIS_TAC [APPEND_ASSOC, APPEND_NIL, everyNotTwice, EVERY_DEF, NOT_EVERY] THEN

      (MAP_EVERY Q.EXISTS_TAC [`p ++ [l1 ++ [NTS n] ++ l2 ++ [NTS A] ++ s0] ++ r1`,
			      `r2`] THEN SRW_TAC [][] THEN
      `r2 ≠ []` by
      (SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       `EVERY isTmnlSym (l1 ++ tl ++ [NTS A] ++ s0)`
       by METIS_TAC [last_elem, APPEND, APPEND_ASSOC] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
      `FRONT (r1 ++ [l1 ++ tl ++ [NTS A] ++ s0] ++ r2) =
      (r1 ++ [l1 ++ tl ++ [NTS A] ++ s0] ++ FRONT r2)`
      by METIS_TAC [frontAppendFst, APPEND_FRONT_LAST, APPEND_ASSOC]
      THENL[
	    METIS_TAC [everyNotTwice, NOT_EVERY, APPEND_NIL],
	    METIS_TAC [everyNotTwice, NOT_EVERY, APPEND_NIL],

	    SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [NOT_EVERY, everyNotTwice, frontAppendFst, APPEND,
		       existsThrice]])]);


val memld = store_thm
("memld",
``R ⊢ dl ◁ x → y ⇒ MEM x dl ∧ MEM y dl``,

Cases_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [last_append, APPEND, APPEND_FRONT_LAST, MEM_APPEND,MEM]);


val listDerivLastBrk = store_thm
("listDerivLastBrk",
``R ⊢ l ++ [e] ◁  x → z ∧ (l ≠ [])
 ⇒
R ⊢ l ◁ x → LAST l ∧ (e = z) ∧ R (LAST l) e``,

SRW_TAC [][listderiv_def] THEN1
METIS_TAC [rtc2list_distrib_append_fst] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
`l=FRONT l ++ [LAST l]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`rtc2list R ([LAST l]++[e])`
 by METIS_TAC [MEM, MEM_APPEND, rtc2list_distrib_append_snd, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) []);

val ldImprtc2list = store_thm
("ldImprtc2list",
``∀dl x y.R ⊢ dl ◁ x → y ⇒ R^* x y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
RES_TAC THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC [RTC_RULES]);



val ldStreams = store_thm
("ldStreams",
``∀dl x1 x2 y.
lderives g ⊢ dl ◁ (x1++x2) → y ∧ isWord y ⇒
∃dl1 dl2 y1 y2.
lderives g ⊢ dl1 ◁ x1 → y1 ∧
lderives g ⊢ dl2 ◁ x2 → y2 ∧
(y = y1 ++ y2) ∧
(dl = MAP (λl.addLast l x2) dl1 ++ MAP (addFront y1) (TL dl2))``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  MAP_EVERY Q.EXISTS_TAC [`[x1]`,`[x2]`] THEN
  FULL_SIMP_TAC (srw_ss()) [addLast_def]) THEN
`h = x1++x2` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
IMP_RES_TAC listDerivHdBrk THEN
FULL_SIMP_TAC (srw_ss()) [lderives] THEN
SRW_TAC [][] THEN
IMP_RES_TAC twoListAppEq THEN SRW_TAC [][]
THENL[
      FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs`,`s2`,`y`] MP_TAC) THEN SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`[s1++[NTS lhs]]++dl1`,`dl2`,`y1`,`y2`] THEN
      SRW_TAC [][addLast_def] THEN
      Cases_on `dl1` THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def, addLast_def] THEN
      SRW_TAC [][] THEN
      METIS_TAC [ldres1, APPEND_NIL, lderives_same_append_left],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
	    FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`rhs++s2`,`y`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    MAP_EVERY Q.EXISTS_TAC [`dl1`,`[NTS lhs::s2]++dl2`,`y1`,`y2`] THEN
	    SRW_TAC [][addLast_def] THEN
	    Cases_on `dl2` THEN
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def, addLast_def] THEN
	    SRW_TAC [][] THEN1
	    METIS_TAC [ldres1, APPEND_NIL, lderives_same_append_right, APPEND] THEN
	    Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
	    `t''=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
	    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND, APPEND_ASSOC],

	    FIRST_X_ASSUM (Q.SPECL_THEN [`x1`,`s1''++rhs++s2`,`y`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    MAP_EVERY Q.EXISTS_TAC [`dl1`,`[s1''++[NTS lhs]++s2]++dl2`,`y1`,
				    `y2`] THEN SRW_TAC [][] THEN
	    Cases_on `dl2` THEN
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def, addLast_def] THEN
	    SRW_TAC [][] THEN1
	    METIS_TAC [ldres1, APPEND_NIL, lderives_same_append_right, APPEND,
		       lderives_same_append_left] THEN
	    Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    `t''=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
	    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [addLast_def] THEN
	    METIS_TAC [APPEND, APPEND_ASSOC],

	    Cases_on `s1''` THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
	    THENL[
		  FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`rhs++s2`,`y`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  MAP_EVERY Q.EXISTS_TAC [`dl1`,`[NTS lhs::s2]++dl2`,`y1`,`y2`] THEN
		  SRW_TAC [][addLast_def] THEN
		  Cases_on `dl2` THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def, addLast_def] THEN
		  SRW_TAC [][] THEN1
		  METIS_TAC [ldres1, APPEND_NIL, lderives_same_append_right, APPEND] THEN
		  Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
		  `t''=[]` by METIS_TAC [rtc2listRtcldTmnls] THEN
		  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [APPEND, APPEND_ASSOC],

		  FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs`,`s2`,`y`] MP_TAC) THEN SRW_TAC [][] THEN
		  MAP_EVERY Q.EXISTS_TAC [`[s1++[NTS lhs]]++dl1`,`dl2`,`y1`,`y2`] THEN
		  SRW_TAC [][addLast_def] THEN
		  Cases_on `dl1` THEN
		  FULL_SIMP_TAC (srw_ss()) [listderiv_def, addLast_def] THEN
		  SRW_TAC [][] THEN
		  METIS_TAC [ldres1, APPEND_NIL, lderives_same_append_left]
		  ]
	    ],


      FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs++s1'`,`s2'`,`y`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `∃dl1 dl2 y1 y2.
            lderives g ⊢ dl1 ◁ s1 ++ rhs ++ s1' → y1 ∧
            lderives g ⊢ dl2 ◁ s2' → y2 ∧ (y = y1 ++ y2) ∧
            ((s1 ++ rhs ++ s1' ++ s2')::t =
             MAP (λl. addLast l s2') dl1 ++
             MAP (addFront y1) (TL dl2))` by METIS_TAC [APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`(s1++[NTS lhs]++s1')::dl1`,`dl2`,`y1`,`y2`] THEN
      SRW_TAC [][] THEN
      Cases_on `dl1` THEN Cases_on `dl2` THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def,addLast_def] THEN
      METIS_TAC [lderives_same_append_left, lderives_same_append_right, ldres1]
      ]);


val rulesets_the_same_derives = store_thm
("rulesets_the_same_derives",
  ``(set (rules g1) = set (rules g2)) ⇒ (derives g1 x y ⇔ derives g2 x y)``,
  SRW_TAC [][derives_def, EXTENSION]);

val rulesets_the_same_RTC_derives = store_thm
("rulesets_the_same_RTC_derives",
  ``(set (rules g1) = set (rules g2)) ⇒
      ((derives g1)^* x y ⇔ (derives g2)^* x y)``,
  Q_TAC SUFF_TAC `
    ∀g1 g2. (set (rules g1) = set (rules g2)) ⇒
            ∀x y. (derives g1)^* x y ⇒ (derives g2)^* x y
  ` THEN1 METIS_TAC [] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [RTC_RULES, rulesets_the_same_derives]);

val rulesets_the_same = store_thm
("rulesets_the_same",
  ``(startSym g1 = startSym g2) ∧ (set (rules g1) = set (rules g2)) ⇒
    (language g1 = language g2)``,
  STRIP_TAC THEN SRW_TAC [][language, EXTENSION] THEN
  METIS_TAC [rulesets_the_same_RTC_derives]);

val derivesImplderives = store_thm
("derivesImplderives",
``∀x y. (derives g)^* x y ⇒ isWord y ⇒ (lderives g)^* x y``,

SRW_TAC [][] THEN
`∃n.NRC (derives g) n x y`
by
(IMP_RES_TAC rtc2list_exists' THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
`LENGTH t < LENGTH (h::t)` by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
IMP_RES_TAC listderivNrc THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
 Q.EXISTS_TAC `0` THEN
 SRW_TAC [][arithmeticTheory.NRC]) THEN

FIRST_X_ASSUM (Q.SPECL_THEN [`y`, `h'`,`derives g`] MP_TAC) THEN SRW_TAC [][] THEN
IMP_RES_TAC listDerivHdBrk THEN
RES_TAC THEN
Q.EXISTS_TAC `SUC m` THEN
 SRW_TAC [][arithmeticTheory.NRC]  THEN
`h=x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC []) THEN

IMP_RES_TAC nrc_drdeq_ld THEN
METIS_TAC [arithmeticTheory.RTC_eq_NRC]);


val mlDir = "./theoryML/"

(* val _ =
 let open EmitML
 in emitML mlDir
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
*)
val _ = export_theory ();
