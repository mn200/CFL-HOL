(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory relationTheory listTheory
open pred_setTheory symbolDefTheory grammarDefTheory listLemmasTheory eProdsTheory
    containerLemmasTheory
open reachableGrammarTheory

val _ = new_theory "unitProds"

(* Rules of the form A->B, where A and B are in nonTerminals g *)
val unitProds = Define
`unitProds g = {rule l r | ∃nt.(r=[NTS nt]) ∧ MEM (rule l r) (rules g)}`;

(* A->*B where A and B are in nonTerminals g *)
val allDeps = Define `allDeps g =
{(a,b) |  RTC (derives g) [a] [b] ∧
 a ∈ (allSyms g) ∧ b ∈ (allSyms g) }`;

val nonUnitProds = Define
`nonUnitProds g = (LIST_TO_SET (rules g)) DIFF (unitProds g)`;

val newProds = Define
`newProds (g:(α,β) grammar) (p':(α,β) rule -> bool) =
{rule a r | ∃b ru.(rule b r ∈ p' ∧
		(NTS a,NTS b) IN allDeps (G ru (startSym g)) ∧
		(set ru = unitProds g))}`;

val upgr_rules = Define
`(upgr_rules g =  (nonUnitProds g) ∪ (newProds g (nonUnitProds g)))`;

val upgr = Define
`upgr g g' <=>
  (set (rules g') = upgr_rules g) ∧
  (startSym g' = startSym g)`;


val finiteallDeps = store_thm
("finiteallDeps",
``FINITE (allDeps g)``,

SRW_TAC [][allDeps] THEN
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
 Q.ABBREV_TAC `f = \sym:(α,β) symbol.
			{ (sym,b) | b |
			 (derives g)^* [sym] [b] ∧  b ∈ allSyms g}` THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f (allSyms g))`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	`FINITE (allSyms g)` by METIS_TAC [FINITE_LIST_TO_SET, finiteAllSyms] THEN
	SRW_TAC [][] THEN
	Q.ABBREV_TAC `h = \s:(α,β) symbol. if (derives g)^* [sym] [s] then {(sym,s)}
                                        	else {}` THEN
	Q.MATCH_ABBREV_TAC `FINITE Horrible2` THEN
	Q_TAC SUFF_TAC `Horrible2 = BIGUNION (IMAGE h (allSyms g))` THEN1
	(DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`h`] THEN
	Cases_on `(derives g)^* [sym] [s']` THEN SRW_TAC [][]) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`h`, Abbr`Horrible2`] THEN
	METIS_TAC []) THEN
	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`f`, Abbr`Horrible`] THEN
	METIS_TAC []);



val rulesets_the_same_allSyms = store_thm
("rulesets_the_same_allSyms",
``(set ru = set ru') ⇒
(allSyms (G ru s)  = allSyms (G ru' s))``,

SRW_TAC [][allSyms_def, EQ_IMP_THM, nonTerminals_def, terminals_def]);


val finiteunitProds = store_thm
("finiteunitProds",
``FINITE (unitProds g)``,

SRW_TAC [][unitProds] THEN
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
Q.ABBREV_TAC `f = \r. case (r : (α,β)rule) of
                        rule N rhs => if (∃nt. rhs = [NTS nt]) then {rule N rhs}
				      else {}`  THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f (set (rules g)))`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	Cases_on `r` THEN SRW_TAC [][]) THEN
 ONCE_REWRITE_TAC [EXTENSION] THEN
 SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
	    boolSimps.CONJ_ss][EXISTS_rule,
			       Abbr`f`, Abbr`Horrible`] THEN
   METIS_TAC [] );


val finiteallDepsSub = store_thm
("finiteallDepsSub",
``FINITE
{a | ∃ru. (NTS a,NTS n) ∈ allDeps (G ru (startSym g)) ∧ (set ru = unitProds g)}``,

SRW_TAC [][] THEN
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
SRW_TAC [][] THEN
 Q.ABBREV_TAC `f = \(a:(α,β) symbol,b:(α,β) symbol).
                      if (b ≠ NTS n) then {}
			  else { e | (NTS e = a) }` THEN
`FINITE (unitProds g)` by METIS_TAC [finiteunitProds] THEN
`∃ru. set ru = unitProds g` by METIS_TAC [listExists4Set] THEN
 Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f (allDeps (G ru (startSym g))))`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN1
	(`FINITE (allDeps (G ru (startSym g)))` by METIS_TAC [finiteallDeps] THEN
	 SRW_TAC [][]) THEN
	Cases_on `x` THEN
	SRW_TAC [][] THEN
	Cases_on `q` THEN SRW_TAC [][]) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`f`, Abbr`Horrible`] THEN
	SRW_TAC [][EQ_IMP_THM] THEN1

	(Q.EXISTS_TAC `(NTS x, NTS n)` THEN
	 SRW_TAC [][] THEN
	 FULL_SIMP_TAC (srw_ss()) [allDeps] THEN
	 SRW_TAC [][] THEN1
	 METIS_TAC [rulesets_the_same_RTC_derives, rules_def] THEN
	 METIS_TAC [rulesets_the_same_allSyms]) THEN

	Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `r=NTS n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	SRW_TAC [][] THEN
	METIS_TAC []);


val finiteupgrRules = store_thm
("finiteupgrRules",
``FINITE (upgr_rules g)``,

SRW_TAC [][upgr_rules] THEN1
 SRW_TAC [][nonUnitProds] THEN
`FINITE (nonUnitProds g)` by SRW_TAC [][nonUnitProds] THEN
Q.ABBREV_TAC `l = nonUnitProds g` THEN
SRW_TAC [][newProds] THEN
 Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
 Q.ABBREV_TAC `f = \r. case (r : (α,β) rule) of
                        rule N rhs =>
			{ rule a rhs | a |
			 ∃ru. (NTS a,NTS N) ∈ allDeps (G ru (startSym g)) ∧
			 (set ru = unitProds g)} `
 THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f l)`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
	Cases_on `r` THEN SRW_TAC [][] THEN
	Q.MATCH_ABBREV_TAC `FINITE Horrible2` THEN
	Q.ABBREV_TAC `ad = { a | a|  ∃ru.
			    (NTS a,NTS n) ∈ allDeps (G ru (startSym g)) ∧
			     (set ru = unitProds g)}` THEN
	Q_TAC SUFF_TAC `Horrible2 = IMAGE (λe.rule e l') ad` THEN1

	(DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`ad`, Abbr `Horrible2`] THEN
	 METIS_TAC [finiteallDepsSub]) THEN

	ONCE_REWRITE_TAC [EXTENSION] THEN
	SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
		 boolSimps.CONJ_ss][EXISTS_rule,
				    Abbr`Horrible2`, Abbr`ad`]) THEN
 ONCE_REWRITE_TAC [EXTENSION] THEN
 SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
	    boolSimps.CONJ_ss][EXISTS_rule,
			       Abbr`f`, Abbr`Horrible`] THEN
   METIS_TAC [rule_11]);


val upgr_exists = store_thm
("upgr_exists",
``∀g.∃g'.upgr g g'``,

SRW_TAC [][upgr] THEN
METIS_TAC [finiteupgrRules, listExists4Set, startSym_def, rules_def]);


val eq_supgr = prove(
``upgr g g' ⇒ (startSym g = startSym g')``,
Cases_on `g` THEN METIS_TAC [startSym_def,upgr]);


val eq_sneup = prove(
``negr g0 g ⇒ upgr g g' ⇒ (startSym g = startSym g')``,
Cases_on `g` THEN METIS_TAC [startSym_def,upgr,negr_def]);

val eq_sneup1rgr = prove(
``rgr g0 g1 ⇒ negr g1 g2 ⇒ upgr g2 g3 ⇒ (startSym g0 = startSym g3)``,
Cases_on `g0` THEN METIS_TAC [startSym_def,upgr,negr_def, rgr_def]);

val eq_sneup1 = prove(
``negr g1 g2 ⇒ upgr g2 g3 ⇒ (startSym g1 = startSym g3)``,
Cases_on `g1` THEN METIS_TAC [startSym_def,upgr,negr_def, rgr_def]);

(*
Theorem 4.4
Every CFL without e is defined by a grammar with no useless
symbols,e-productions, or unit productions.
*)

val memNonUnitProds = store_thm
("memNonUnitProds",
``e ∈ nonUnitProds g ⇒ MEM e (rules g)``,

SRW_TAC [][nonUnitProds]);

val gsubDeriv = store_thm
("gsubDeriv",
``(∀e.MEM e (rules g) ⇒ MEM e (rules g')) ⇒
derives g v v' ⇒ derives g' v v'``,

SRW_TAC [][derives_def] THEN
METIS_TAC []);

val gsubRtcDeriv = store_thm
("gsubRtcDeriv",
``∀v v'.RTC (derives g) v v' ⇒ (∀e.MEM e (rules g) ⇒ MEM e (rules g')) ⇒
 RTC (derives g') v v'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [RTC_RULES, gsubDeriv]);


val upgr_r3 = prove
(``∀v v'.negr g0 g ⇒ upgr g g' ⇒
derives g' v v' ⇒ RTC (derives g) v v'``,

SRW_TAC [] [derives_def, upgr, rules_def, nonUnitProds,newProds,allDeps,
	    upgr_rules,EXTENSION]
THENL[
 METIS_TAC [res1,derives_same_append_left,derives_same_append_right,RTC_SUBSET],

Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
`∀e.e ∈ unitProds (G l n) ⇒ MEM e (rules (G l n))`
      by  (FULL_SIMP_TAC (srw_ss()) [rules_def, unitProds, EXTENSION] THEN
	   METIS_TAC []) THEN
`RTC (derives (G l n)) [NTS lhs] [NTS b]` by METIS_TAC [gsubRtcDeriv, rules_def] THEN
`derives (G l n) [NTS b] rhs` by METIS_TAC [res1] THEN
FULL_SIMP_TAC (srw_ss()) [eq_sneup,startSym_def,rules_def] THEN
`RTC (derives (G l n)) [NTS lhs] rhs`
      by METIS_TAC [RTC_RULES_RIGHT1,eq_sneup,eq_snegr,negr_def,
		    rules_def] THEN
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left]]);


val upgr_r31 = prove
(``∀v v'. negr g1 g2 ⇒ upgr g2 g3 ⇒
derives g3 v v' ⇒ RTC (derives g2) v v'``,

SRW_TAC [][derives_def, upgr, upgr_rules, rules_def,EXTENSION] THEN1
 (FULL_SIMP_TAC (srw_ss()) [nonUnitProds] THEN
  METIS_TAC [res1,derives_same_append_left,derives_same_append_right,
	     RTC_SUBSET]) THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,newProds,allDeps,unitProds,EXTENSION] THEN
Cases_on `g2` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
`∀e.e ∈ unitProds (G l n) ⇒ MEM e (rules (G l n))`
      by  (FULL_SIMP_TAC (srw_ss()) [rules_def, unitProds, EXTENSION] THEN
	   METIS_TAC []) THEN
`RTC (derives (G l n)) [NTS lhs] [NTS b]` by METIS_TAC [gsubRtcDeriv, rules_def] THEN
`derives (G l n) [NTS b] rhs` by METIS_TAC [res1] THEN
FULL_SIMP_TAC (srw_ss()) [eq_sneup,startSym_def,rules_def] THEN
`RTC (derives (G l n)) [NTS lhs] rhs`
      by METIS_TAC [RTC_RULES_RIGHT1,eq_sneup,eq_snegr,negr_def,
		    rules_def] THEN
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left]);


val upgr_r31rgr = prove
(``∀v v'.rgr g0 g1 ⇒ negr g1 g2 ⇒ upgr g2 g3 ⇒
derives g3 v v' ⇒ RTC (derives g2) v v'``,

SRW_TAC [] [derives_def, upgr, rules_def, nonUnitProds,newProds,allDeps,
	    upgr_rules,EXTENSION]
THENL[
 METIS_TAC [res1,derives_same_append_left,derives_same_append_right,RTC_SUBSET],

Cases_on `g2` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
`∀e.e ∈ unitProds (G l n) ⇒ MEM e (rules (G l n))`
      by  (FULL_SIMP_TAC (srw_ss()) [rules_def, unitProds, EXTENSION] THEN
	   METIS_TAC []) THEN
`RTC (derives (G l n)) [NTS lhs] [NTS b]` by METIS_TAC [gsubRtcDeriv, rules_def] THEN
`derives (G l n) [NTS b] rhs` by METIS_TAC [res1] THEN
FULL_SIMP_TAC (srw_ss()) [eq_sneup,startSym_def,rules_def] THEN
`RTC (derives (G l n)) [NTS lhs] rhs`
      by METIS_TAC [RTC_RULES_RIGHT1,eq_sneup,eq_snegr,negr_def,
		    rules_def] THEN
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left]]);

val upgr_r2 = prove(
``∀u v.RTC (derives g') u v ⇒ negr g0 g ⇒ upgr g g' ⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES,upgr_r3, RTC_RTC]);

val upgr_r21rgr = prove(
``∀u v.RTC (derives g3) u v ⇒ rgr g0 g1 ⇒ negr g1 g2 ⇒ upgr g2 g3
⇒ RTC (derives g2) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES,upgr_r31, RTC_RTC]);

val upgr_r21 = prove(
``∀u v.RTC (derives g3) u v ⇒ negr g1 g2 ⇒ upgr g2 g3
⇒ RTC (derives g2) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES,upgr_r31, RTC_RTC]);


val upgr_r4 = store_thm("upgr_r4",
``∀u v.RTC (derives g') u v ⇒
negr g0 g ⇒ upgr g g' ⇒
RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [upgr_r3,RTC_RTC]);

val upgr_r41 = store_thm("upgr_r41",
``∀u v.RTC (derives g3) u v ⇒  negr g1 g2 ⇒ upgr g2 g3 ⇒
RTC (derives g2) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [upgr_r3,RTC_RTC]);

val upgr_r41rgr = store_thm("upgr_r41rgr",
``∀u v.RTC (derives g3) u v ⇒
rgr g0 g1 ⇒ negr g1 g2 ⇒ upgr g2 g3 ⇒
RTC (derives g2) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [upgr_r3,RTC_RTC]);


val upgr_r5 = prove(
``derives g v v' ⇒
negr g0 g ⇒ upgr g g' ⇒ EVERY isTmnlSym v' ⇒ derives g' v v'``,

SRW_TAC [] [derives_def,nonUnitProds,newProds,allDeps] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,unitProds] THEN
SRW_TAC [] [] THEN
`∀e. MEM e rhs ⇒ isTmnlSym e` by FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
`~∃nt.(rhs = [] ++ [NTS nt] ++ []) ∧ isNonTmnlSym (NTS nt)`
		    by METIS_TAC [sym_r3,isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [upgr, upgr_rules,nonUnitProds,unitProds,EXTENSION] THEN
METIS_TAC [symbol_11,isNonTmnlSym_def]);



val upgr_r5rgr = prove(
``derives g v v' ⇒
rgr gr g0 ⇒ negr g0 g ⇒ upgr g g' ⇒ EVERY isTmnlSym v' ⇒ derives g' v v'``,

SRW_TAC [] [derives_def,nonUnitProds,newProds,allDeps] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,unitProds] THEN
SRW_TAC [] [] THEN
`∀e. MEM e rhs ⇒ isTmnlSym e` by FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
`~∃nt.(rhs = [] ++ [NTS nt] ++ []) ∧ isNonTmnlSym (NTS nt)`
		    by METIS_TAC [sym_r3,isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [upgr, upgr_rules,nonUnitProds,unitProds,EXTENSION] THEN
METIS_TAC [symbol_11,isNonTmnlSym_def]);

val upgr_r6 = prove(
``RTC (derives g) [NTS x] [NTS y] ⇒ negr g0 g ⇒
(NTS x IN nonTerminals g) ⇒ (NTS y IN nonTerminals g)  ⇒
(NTS x,NTS y) IN (allDeps g)``,

SRW_TAC [] [allDeps] THEN SRW_TAC [] [allSyms_def]);

val upgr_r6rgr = prove(
``RTC (derives g) [NTS x] [NTS y] ⇒ rgr gr g0 ⇒ negr g0 g ⇒
(NTS x IN nonTerminals g) ⇒ (NTS y IN nonTerminals g)  ⇒
(NTS x,NTS y) IN (allDeps g)``,

SRW_TAC [] [allDeps] THEN SRW_TAC [] [allSyms_def]);


val negr_r16 = prove(
``∀v v'.negr g0 g ⇒ derives g v v' ⇒ ~(v'=[])``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,negr_def,munge_def,EXTENSION] THEN
SRW_TAC [][] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []);


val negr_r17 = prove(
``negr g0 g ⇒ MEM (rule l r) (rules g) ⇒ ~(r=[])``,
SRW_TAC [] [negr_def,munge_def,EXTENSION]);


val eqSymsToStr = Define
`(eqSyms (NTS nt1) (NTS nt2) = (nt1=nt2)) ∧
 (eqSyms (TS ts1) (TS ts2) = (ts1=ts2))`;



val rel_r1 = prove(
``∀x y.RTC R x y ∧ ~(x=y) ⇒ TC R x y``,
SRW_TAC [] [] THEN
`RC R x y ∨ TC R x y` by METIS_TAC [RTC_TC_RC]  THEN
FULL_SIMP_TAC (srw_ss()) [RC_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_TRANSITIVE,TC_DEF]);


val upgr_r8 = prove(
``negr g0 g ⇒ upgr g g' ⇒
  derives g [NTS lhs] [NTS nt] ⇒ derives g [NTS nt] r
  ⇒ ~(∃n.r=[NTS n]) ⇒ derives g' [NTS lhs] r``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(s1=[]) ∧ (s2=[]) ∧ (s1'=[]) ∧ (s2'=[])` by METIS_TAC [lres] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,allDeps,newProds, upgr_rules,upgr,
			  EXTENSION] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `lhs''` THEN
SRW_TAC [][] THEN
`FINITE (unitProds g)` by METIS_TAC [finiteunitProds] THEN
`∃ru. set ru = unitProds g` by METIS_TAC [listExists4Set] THEN
Q.EXISTS_TAC `ru` THEN
SRW_TAC [][] THEN1 FULL_SIMP_TAC (srw_ss()) [unitProds] 

 >- (`rule lhs [NTS lhs''] ∈ (unitProds g)` by SRW_TAC [][unitProds] THEN
     METIS_TAC [res1, RTC_RULES, rules_def, startSym_def, mem_in])

 >- (SRW_TAC [][allSyms_def] THEN
     `rule lhs [NTS lhs''] ∈ (unitProds g)` by SRW_TAC [][unitProds] THEN
     METIS_TAC [startSym_def, rules_def, slemma1_4, symbol_11, mem_in])

 >- (SRW_TAC [][allSyms_def] THEN
     `rule lhs [NTS lhs''] ∈ (unitProds g)` by SRW_TAC [][unitProds] THEN
     METIS_TAC [startSym_def, rules_def, slemma1_4, symbol_11, mem_in, 
                APPEND_NIL,APPEND])
);

val upgr_r8rgr = prove(
``rgr gr g0 ⇒ negr g0 g ⇒ upgr g g' ⇒
derives g [NTS lhs] [NTS nt] ⇒ derives g [NTS nt] r ⇒
		    ~(∃n.r=[NTS n]) ⇒ derives g' [NTS lhs] r``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(s1=[]) ∧ (s2=[]) ∧ (s1'=[]) ∧ (s2'=[])` by METIS_TAC [lres] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,allDeps,newProds, upgr_rules,upgr,
			  EXTENSION] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `lhs''` THEN
SRW_TAC [][] THEN
`FINITE (unitProds g)` by METIS_TAC [finiteunitProds] THEN
`∃ru. set ru = unitProds g` by METIS_TAC [listExists4Set] THEN
Q.EXISTS_TAC `ru` THEN
SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [unitProds] THENL[

`rule lhs [NTS lhs''] ∈ (unitProds g)` by SRW_TAC [][unitProds] THEN
METIS_TAC [res1, RTC_RULES, rules_def, startSym_def, mem_in],

SRW_TAC [][allSyms_def] THEN
`rule lhs [NTS lhs''] ∈ (unitProds g)` by SRW_TAC [][unitProds] THEN
METIS_TAC [startSym_def, rules_def, slemma1_4, symbol_11, mem_in],

SRW_TAC [][allSyms_def] THEN
`rule lhs [NTS lhs''] ∈ (unitProds g)` by SRW_TAC [][unitProds] THEN
METIS_TAC [startSym_def, rules_def, slemma1_4, symbol_11, mem_in, APPEND_NIL,
	   APPEND]
]);


val upgr_r9 = prove
(``upgr g0 g ⇒ derives g [NTS n] v ∧ (∀e.MEM e ru ⇔ e ∈ unitProds g0) ⇒
∃nt. RTC (derives (G ru (startSym g0))) [NTS n] [NTS nt] ∧
 derives g0 [NTS nt] v``,

SRW_TAC [] [derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [upgr, upgr_rules,EXTENSION] THEN
`rule lhs rhs ∈ nonUnitProds g0 ∨
 rule lhs rhs ∈ newProds g0 (nonUnitProds g0)` by METIS_TAC []
  >- (Q.EXISTS_TAC `lhs` THEN
       SRW_TAC [] [RTC_RULES] THEN
       FULL_SIMP_TAC (srw_ss()) [nonUnitProds] THEN
       MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`] THEN
       SRW_TAC [] [])
  >- (FULL_SIMP_TAC (srw_ss()) [newProds,allDeps] THEN
       Q.EXISTS_TAC `b` THEN
       SRW_TAC [] [] THEN
       `set ru = set ru'` by FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
       FULL_SIMP_TAC (srw_ss()) [nonUnitProds] THEN
       METIS_TAC [rulesets_the_same_RTC_derives, mem_in, rules_def])
);


val upgr_r10 = prove
(``negr g0 g ⇒ derives g [NTS nt1] [NTS nt2] ∧
(∀e.MEM e ru ⇔ e ∈ unitProds g) ⇒
derives (G ru (startSym g)) [NTS nt1] [NTS nt2]``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
SRW_TAC [] [rules_def,unitProds] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] []);


val upgr_r10rgr = prove
(``rgr gr g0 ⇒ negr g0 g ⇒ derives g [NTS nt1] [NTS nt2] ∧
(∀e.MEM e ru ⇔ e ∈ unitProds g) ⇒
derives (G ru (startSym g)) [NTS nt1] [NTS nt2]``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
SRW_TAC [] [rules_def,unitProds] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] []);


val upgr_r12 = prove(
``upgr g0 g ⇒ MEM (rule l r) (rules g) ⇒ rule l r ∉ unitProds g0``,
SRW_TAC [] [unitProds,upgr_rules, upgr,EXTENSION] THENL[
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN METIS_TAC [],
FULL_SIMP_TAC (srw_ss()) [newProds,nonUnitProds,allDeps,unitProds,
			  EXTENSION] THEN
METIS_TAC []]);



val upgr_r13 = prove(
``upgr g0 g ⇒ MEM (rule l r) (rules g) ⇒ ∃n.r≠[NTS n]``,
SRW_TAC [] [] THEN
`rule l r ∉ unitProds g0` by METIS_TAC [upgr_r12] THEN
FULL_SIMP_TAC (srw_ss()) [unitProds,upgr, upgr_rules,EXTENSION] THEN
RES_TAC
THENL[
      FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN
      METIS_TAC [],
      FULL_SIMP_TAC (srw_ss()) [nonUnitProds,newProds,allDeps,unitProds] THEN
      METIS_TAC []]);


val upgr_r14 = prove(
``negr g0 g ⇒ derives g [NTS nt1] [NTS nt2] ⇒ upgr g g' ⇒
derives g' [NTS nt2] v ⇒ derives g' [NTS nt1] v``,

SRW_TAC [] [] THEN
`FINITE (unitProds g)` by METIS_TAC [finiteunitProds] THEN
`∃ru. set ru = unitProds g` by METIS_TAC [listExists4Set] THEN
`derives (G ru (startSym g)) [NTS nt1] [NTS nt2]` by METIS_TAC [upgr_r10,
								mem_in] THEN
`∃nt.(derives (G ru (startSym g)))^* [NTS nt2] [NTS nt] ∧
		     derives g [NTS nt] v` by METIS_TAC [upgr_r9, mem_in] THEN
`RTC (derives (G ru (startSym g))) [NTS nt1] [NTS nt]`
		     by METIS_TAC [RTC_RULES] THEN
SRW_TAC [] [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`v`,`nt1`] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [upgr, upgr_rules] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
`rule nt1 v ∈ newProds g (nonUnitProds g)` by

(SRW_TAC [][newProds] THEN
`rule nt v ∈ nonUnitProds g` by
(SRW_TAC [][nonUnitProds, unitProds] THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN
 SRW_TAC [][] THEN
 `rule nt2 [NTS nt'] ∈ nonUnitProds g ∪ newProds g (nonUnitProds g)`
 by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [nonUnitProds, unitProds] THEN
 FULL_SIMP_TAC (srw_ss()) [newProds]) THEN

`(NTS nt1, NTS nt) ∈ allDeps (G ru (startSym g))` by
(SRW_TAC [][allDeps, allSyms_def] THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds] THEN1
METIS_TAC [slemma1_4, startSym_def, mem_in ,rules_def] THEN
`LENGTH [NTS nt] ≥ 1` by SRW_TAC [][] THEN
Cases_on `nt1 = nt` THEN SRW_TAC [][] THEN
METIS_TAC [slemma1_4, startSym_def, mem_in ,rules_def,
	   rtcDerivesInRuleRhsLenGte1, MEM]) THEN
METIS_TAC []) THEN

FULL_SIMP_TAC (srw_ss()) [EXTENSION]);


val upgr_r14rgr = prove(
``rgr gr g0 ⇒ negr g0 g ⇒ derives g [NTS nt1] [NTS nt2] ⇒ upgr g g' ⇒
derives g' [NTS nt2] v ⇒ derives g' [NTS nt1] v``,

SRW_TAC [] [] THEN
`FINITE (unitProds g)` by METIS_TAC [finiteunitProds] THEN
`∃ru. set ru = unitProds g` by METIS_TAC [listExists4Set] THEN
`derives (G ru (startSym g)) [NTS nt1] [NTS nt2]` by METIS_TAC [upgr_r10,
								mem_in] THEN
`∃nt.(derives (G ru (startSym g)))^* [NTS nt2] [NTS nt] ∧
		     derives g [NTS nt] v` by METIS_TAC [upgr_r9, mem_in] THEN
`RTC (derives (G ru (startSym g))) [NTS nt1] [NTS nt]`
		     by METIS_TAC [RTC_RULES] THEN
SRW_TAC [] [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`v`,`nt1`] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [upgr, upgr_rules] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
`rule nt1 v ∈ newProds g (nonUnitProds g)` by

(SRW_TAC [][newProds] THEN
`rule nt v ∈ nonUnitProds g` by
(SRW_TAC [][nonUnitProds, unitProds] THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN
 SRW_TAC [][] THEN
 `rule nt2 [NTS nt'] ∈ nonUnitProds g ∪ newProds g (nonUnitProds g)`
 by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [nonUnitProds, unitProds] THEN
 FULL_SIMP_TAC (srw_ss()) [newProds]) THEN

`(NTS nt1, NTS nt) ∈ allDeps (G ru (startSym g))` by
(SRW_TAC [][allDeps, allSyms_def] THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds] THEN1
METIS_TAC [slemma1_4, startSym_def, mem_in ,rules_def] THEN
`LENGTH [NTS nt] ≥ 1` by SRW_TAC [][] THEN
Cases_on `nt1 = nt` THEN SRW_TAC [][] THEN
METIS_TAC [slemma1_4, startSym_def, mem_in ,rules_def,
	   rtcDerivesInRuleRhsLenGte1, MEM]) THEN
METIS_TAC []) THEN

FULL_SIMP_TAC (srw_ss()) [EXTENSION]);


val up_r1 = prove (
``rule lhs (s1++[NTS nt]++s2) ∈ unitProds g 
    <=>
  (s1=[]) ∧ (s2=[]) ∧ rule lhs [NTS nt] ∈ unitProds g``,
SRW_TAC [][EQ_IMP_THM] THENL[

FULL_SIMP_TAC (srw_ss()) [unitProds] THEN METIS_TAC [lres],

FULL_SIMP_TAC (srw_ss()) [unitProds] THEN METIS_TAC [lres],

FULL_SIMP_TAC (srw_ss()) [unitProds] THEN METIS_TAC [lres]]);


val up_r2 = prove(
``negr g0 g ⇒ rule lhs rhs ∈ unitProds g ⇒ MEM (rule lhs rhs) (rules g)``,
SRW_TAC [] [unitProds]);

val up_r2rgr = prove(
``rgr gr g0 ⇒ negr g0 g ⇒ rule lhs rhs ∈ unitProds g ⇒ MEM (rule lhs rhs) (rules g)``,
SRW_TAC [] [unitProds]);

val upgr_r20rgr = store_thm("upgr_r20rgr",
``∀u v.RTC (derives g) u v ⇒ rgr gr g0 ⇒ negr g0 g ∧ upgr g g' ⇒
		     EVERY isTmnlSym v ⇒ RTC (derives g') u v``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`∃s1' rhs' s2'. (v = s1' ++  rhs' ++ s2') ∧ RTC (derives g') s1 s1' ∧
RTC (derives g') rhs rhs' ∧ RTC (derives g') s2 s2'` by SRW_TAC [] [upgr_r19] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND] THEN
`derives g [NTS lhs] rhs` by METIS_TAC [res1] THEN
Cases_on `rhs=rhs'`
THENL[
      SRW_TAC [] [] THEN
      METIS_TAC [derives_append,upgr_r5,RTC_SUBSET,RTC_RULES,RTC_REFLEXIVE],

      `∃sf.derives g' rhs sf ∧ RTC (derives g') sf rhs'` by METIS_TAC [rtc_r1] THEN
      Cases_on `rule lhs rhs ∉ unitProds g`
      THENL[
	    SRW_TAC [] [] THEN
	    `MEM (rule lhs rhs) (rules g')`
	    by (FULL_SIMP_TAC (srw_ss()) [unitProds, upgr, upgr_rules,
					  nonUnitProds,EXTENSION]  THEN
		METIS_TAC []) THEN
	    FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN
	    METIS_TAC [RTC_SUBSET, res1, derives_append,RTC_RULES],


	    SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	    SRW_TAC [] [] THEN
	    `(s1'''=[]) /\ (s2'''=[]) /\ rule lhs [NTS lhs''] ∈ unitProds g`
	    by METIS_TAC [up_r1] THEN
	    `MEM (rule lhs [NTS lhs'']) (rules g)` by METIS_TAC [up_r2] THEN
	    `derives g' [NTS lhs] rhs'''` by METIS_TAC [res1,upgr_r14] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [RTC_RULES,derives_append]]]);


val upgr_r20 = store_thm("upgr_r20",
``∀u v.RTC (derives g) u v ⇒ negr g0 g ∧ upgr g g' ⇒
		     EVERY isTmnlSym v ⇒ RTC (derives g') u v``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`∃s1' rhs' s2'. (v = s1' ++  rhs' ++ s2') ∧ RTC (derives g') s1 s1' ∧
RTC (derives g') rhs rhs' ∧ RTC (derives g') s2 s2'` by SRW_TAC [] [upgr_r19] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND] THEN
`derives g [NTS lhs] rhs` by METIS_TAC [res1] THEN
Cases_on `rhs=rhs'`
THENL[
      SRW_TAC [] [] THEN
      METIS_TAC [derives_append,upgr_r5,RTC_SUBSET,RTC_RULES,RTC_REFLEXIVE],

      `∃sf.derives g' rhs sf ∧ RTC (derives g') sf rhs'` by METIS_TAC [rtc_r1] THEN
      Cases_on `rule lhs rhs ∉ unitProds g`
      THENL[
	    SRW_TAC [] [] THEN
	    `MEM (rule lhs rhs) (rules g')`
	    by (FULL_SIMP_TAC (srw_ss()) [unitProds, upgr, upgr_rules,
					  nonUnitProds,EXTENSION]  THEN
		METIS_TAC []) THEN
	    FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN
	    METIS_TAC [RTC_SUBSET, res1, derives_append,RTC_RULES],


	    SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	    SRW_TAC [] [] THEN
	    `(s1'''=[]) /\ (s2'''=[]) /\ rule lhs [NTS lhs''] ∈ unitProds g`
	    by METIS_TAC [up_r1] THEN
	    `MEM (rule lhs [NTS lhs'']) (rules g)` by METIS_TAC [up_r2] THEN
	    `derives g' [NTS lhs] rhs'''` by METIS_TAC [res1,upgr_r14] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [RTC_RULES,derives_append]]]);



val thm4_4rgr = store_thm("thm4_4rgr",
``[] ∉ language g0 ∧ rgr g0 g1 ∧ negr g1 g2 ∧ upgr g2 g3 ⇒
		   (language g0 = language g3)``,
SRW_TAC [][] THEN
`language g0 = language g1` by METIS_TAC [thm4_2] THEN
`language g1 = language g2` by METIS_TAC [thm4_3] THEN
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM]
THENL[
METIS_TAC [upgr_r20rgr,eq_supgr],
METIS_TAC [upgr_r4,eq_supgr]]);

val thm4_4 = store_thm("thm4_4",
``[] ∉ language g ∧ negr g0 g ∧ upgr g g' ⇒
		   (language g = language g')``,
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM]
THENL[
METIS_TAC [upgr_r20,eq_supgr],
METIS_TAC [upgr_r4,eq_supgr]]);


val _ = export_theory ();
