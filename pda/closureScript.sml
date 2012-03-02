open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory

open listLemmasTheory relationLemmasTheory
     grammarDefTheory pdaDefTheory symbolDefTheory parseTreeTheory
     treeDerivTheory


val _ = new_theory "closure"

val _ = diminish_srw_ss ["list EQ"];


(* Disjoint *)


val stripNts =  Define `stripNts (NTS a) = a`;

val rename = Define `rename x x' e = if (e=x) then x' else e`;

val ruleNt2Nt' = Define
`ruleNt2Nt' nt nt' (rule l r)  =
rule (rename nt nt' l) (MAP (rename (NTS nt) (NTS nt')) r)`;

val grNt2Nt' = Define
`grNt2Nt' nt nt' (G p s) =
G (MAP (ruleNt2Nt' nt nt') p) (rename nt nt' s) `;


val grNt2Nt'R = Define
`grNt2Nt'R (nt:'a,nt':'a) (g:('a,'b) grammar) g' =
   (NTS nt' ∉ nonTerminals g) ∧ (grNt2Nt' nt nt' g = g')`;

val renameListSame = store_thm
("renameListSame",
``¬MEM (NTS nt) l ⇒ (MAP (rename (NTS nt) (NTS nt')) l = l)``,

Induct_on `l` THEN SRW_TAC [][rename]);


val renameRuleSame = store_thm
("renameRuleSame",
``NTS nt ∉ nonTerminals g ∧ MEM ru (rules g)
     ⇒
   (ruleNt2Nt' nt nt' ru = ru)``,

Cases_on `ru` THEN
SRW_TAC [][ruleNt2Nt'] THEN
`¬∃p s.(l=(p ++ [NTS nt] ++ s))` by METIS_TAC [slemma1_4] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [rename, renameListSame, MEM_APPEND, MEM, rgr_r9eq, slemma1_4]);



val derivImpRenameD = store_thm
("derivImpRenameD",
``derives g w w'
        ⇒
     (derives (grNt2Nt' nt nt' g)) (MAP (rename (NTS nt) (NTS nt')) w)
                                   (MAP (rename (NTS nt) (NTS nt')) w')``,

SRW_TAC [][derives_def] THEN
Cases_on `g` THEN
SRW_TAC [][grNt2Nt', rules_def] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (rename (NTS nt) (NTS nt')) s1`,
			`MAP (rename (NTS nt) (NTS nt')) s2`,
			`MAP (rename (NTS nt) (NTS nt')) rhs`,
			`rename nt nt' lhs`] THEN
SRW_TAC [][] THEN1
METIS_TAC [renameListSame, renameRuleSame, rename, symbol_11, rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def, rgr_r9eq, ruleNt2Nt'] THEN
METIS_TAC []);


val renameAllTms = store_thm
("renameAllTms",
``EVERY isTmnlSym w ⇒ (MAP (rename (NTS nt) (NTS nt') ) w = w)``,
Induct_on `w` THEN SRW_TAC [][] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, rename]);


val rtcDerivImpRenameD = store_thm
("rtcDerivImpRenameD",
``∀w w'.(derives g)^* w w'
           ⇒
     (derives (grNt2Nt' nt nt' g))^* (MAP (rename (NTS nt) (NTS nt')) w)
                                     (MAP (rename (NTS nt) (NTS nt')) w')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
`derives (grNt2Nt' nt nt' g) (MAP (rename (NTS nt) (NTS nt')) [NTS lhs])
 (MAP (rename (NTS nt) (NTS nt')) rhs)` by METIS_TAC [res1, derivImpRenameD] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [RTC_RULES, renameAllTms, derives_same_append_left,
	   derives_same_append_right]);

val renameTwice = store_thm
("renameTwice",
``(nt' ≠ n) ⇒ (rename nt' nt (rename nt nt' n) = n)``,

SRW_TAC [] [rename] THEN
METIS_TAC []);

val mapRenameTwice = store_thm
("mapRenameTwice",
``¬MEM (NTS nt') l ⇒
 (MAP (rename (NTS nt') (NTS nt)) (MAP (rename (NTS nt) (NTS nt')) l) = l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
METIS_TAC [renameTwice]);


val nt2nt'ListRuleInG = store_thm
("nt2nt'ListRuleInG",
``∀l.MEM (rule lhs rhs) (MAP (ruleNt2Nt' nt nt') l)  ∧
¬ (∃rhs.MEM (rule nt' rhs) l ∨
        ∃lhs p s.
           MEM (rule lhs (p ++ [NTS nt'] ++ s)) l ∨
           (nt' = startSym g))
         ⇒
      MEM (rule (rename nt' nt lhs) (MAP (rename (NTS nt') (NTS nt)) rhs)) l``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [ruleNt2Nt'] THEN
SRW_TAC [][] THEN
METIS_TAC [MEM, rgr_r9eq, MEM, slemma1_4, renameTwice, mapRenameTwice,
	   rules_def, MEM_APPEND]);


val nt2nt'RuleInG = store_thm
("nt2nt'RuleInG",
``MEM (rule lhs rhs) (rules (grNt2Nt' nt nt' g)) ⇒ (NTS nt') ∉ nonTerminals g
      ⇒
   MEM (rule (rename nt' nt lhs) (MAP (rename (NTS nt') (NTS nt)) rhs)) (rules g)``,

Cases_on `g` THEN
SRW_TAC [][rules_def, grNt2Nt'] THEN
METIS_TAC [slemma1_4, nt2nt'ListRuleInG, rules_def]);



val renameDImpD = store_thm
("renameDImpD",
``derives (grNt2Nt' nt nt' g) w w' ⇒ (NTS nt') ∉ nonTerminals g
       ⇒
     derives g (MAP (rename (NTS nt') (NTS nt)) w)
                   (MAP (rename (NTS nt') (NTS nt)) w')``,

SRW_TAC [][derives_def] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (rename (NTS nt') (NTS nt)) s1`,
			`MAP (rename (NTS nt') (NTS nt)) s2`,
			`MAP (rename (NTS nt') (NTS nt)) rhs`,
			`rename nt' nt lhs`] THEN
SRW_TAC [][] THEN1 SRW_TAC [][rename] THEN
METIS_TAC [nt2nt'RuleInG]);



val renameRtcDImpD = store_thm
("renameRtcDImpD",
``∀w w'.(derives (grNt2Nt' nt nt' g))^* w w' ⇒ (NTS nt') ∉ nonTerminals g
       ⇒
     (derives g)^* (MAP (rename (NTS nt') (NTS nt)) w)
                   (MAP (rename (NTS nt') (NTS nt)) w')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [renameDImpD, RTC_RULES, renameAllTms]);


val nt2nt'LangEq = store_thm
("nt2nt'LangEq",
`` INFINITE (UNIV:'a set)  ⇒ (NTS (nt':'a)) ∉ nonTerminals g
        ⇒
	(language g = language (grNt2Nt' nt nt' g))``,

SRW_TAC [][language_def, EQ_IMP_THM, EXTENSION]
THENL[

      `(derives (grNt2Nt' nt nt' g))^*
      (MAP (rename (NTS nt) (NTS nt')) [NTS (startSym g)]) x`
      by METIS_TAC [renameAllTms, rtcDerivImpRenameD, stripNts] THEN
      Cases_on `g` THEN
      FULL_SIMP_TAC (srw_ss()) [rename, startSym_def, grNt2Nt'] THEN
      METIS_TAC [],

      IMP_RES_TAC renameRtcDImpD THEN
      `NTS nt' ∉ nonTerminals g` by METIS_TAC [stripNts] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `g` THEN
      FULL_SIMP_TAC (srw_ss()) [startSym_def, grNt2Nt', rename] THEN
      Cases_on `n=nt` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [renameAllTms, slemma1_4, stripNts, startSym_def]
      ]);


val ruleNt2Nt'Mem1 = store_thm
("ruleNt2Nt'Mem1",
``MEM (rule nt rhs) l ⇒ ∃rhs'.MEM (rule nt' rhs') (MAP (ruleNt2Nt' nt nt') l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
SRW_TAC [][ruleNt2Nt', rename] THEN
METIS_TAC []);


val renameNtNotMem = store_thm
("renameNtNotMem",
``(nt ≠ nt') ⇒ ¬MEM (NTS nt) (MAP (rename (NTS nt) (NTS nt')) l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN SRW_TAC [][rename]);


val ruleNt2Nt'Repl = store_thm
("ruleNt2Nt'Repl",
``∀l.(nt≠ nt') ∧ MEM (rule lhs rhs) (MAP (ruleNt2Nt' nt nt') l)
   ⇒
  (lhs ≠ nt) ∧ ¬MEM (NTS nt) rhs``,

Induct_on `l` THEN SRW_TAC [][] THEN1
(Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [ruleNt2Nt', rename] THEN
SRW_TAC [][]) THEN1
(Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [ruleNt2Nt'] THEN
SRW_TAC [][] THEN
METIS_TAC [renameNtNotMem]) THEN
METIS_TAC [renameNtNotMem]);


val mapRenameListEq = store_thm
("mapRenameListEq",
``(¬MEM (NTS nt') l) ∧ (l' = (MAP (rename (NTS nt) (NTS nt')) l))
     ⇒
    (l = MAP (rename (NTS nt') (NTS nt)) l')``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [rename] THEN
SRW_TAC [][] THEN
METIS_TAC [symbol_11, mapRenameTwice]);


val renameNtInList = store_thm
("renameNtInList",
``¬MEM (NTS nt') l ⇒
  MEM (NTS nt') (MAP (rename (NTS nt) (NTS nt')) l)
     ⇒
     MEM (NTS nt) l``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [rename] THEN
METIS_TAC [symbol_11]);

val renameNtNeNt'InList = store_thm
("renameNtNeNt'InList",
``(x ≠ nt') ∧
 MEM (NTS x) (MAP (rename (NTS nt) (NTS nt')) l)
     ⇒
     MEM (NTS x) l``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [rename] THEN
METIS_TAC [symbol_11]);


val ruleNt2Nt'MemInOld = store_thm
("ruleNt2Nt'MemInOld",
``MEM (rule lhs (p ++ [NTS x] ++ s)) (MAP (ruleNt2Nt' nt nt') l)
     ⇒
     ((x=nt') ⇒ ((∃lhs' p' s'.MEM (rule lhs' (p'++[NTS nt]++s')) l) ∨
                 (∃lhs' p' s'.MEM (rule lhs' (p'++[NTS nt']++s')) l)))∧
     ((x≠nt') ⇒ ∃lhs' p' s'.MEM (rule lhs' (p'++[NTS x]++s')) l)``,

SRW_TAC [][MEM_MAP] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [ruleNt2Nt'] THEN
SRW_TAC [][] THEN
Cases_on `MEM (NTS nt') l'` THEN
METIS_TAC [rgr_r9eq, MAP_APPEND, rename, symbol_11, renameNtInList,
	   renameNtNeNt'InList]);

val ruleNt2Nt'Mem2 = store_thm
("ruleNt2Nt'Mem2",
``MEM (rule l' (p ++ [NTS nt] ++ s)) l ⇒
 ∃lhs p' s'.MEM (rule lhs (p'++[NTS nt']++s')) (MAP (ruleNt2Nt' nt nt') l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
SRW_TAC [][ruleNt2Nt', rename] THEN
METIS_TAC []);


val grNt2Nt'RSymInRuleG' = store_thm
("grNt2Nt'RSymInRuleG'",
``(nt ≠ nt') ⇒ (NTS nt ∈ nonTerminals g)
       ⇒ grNt2Nt'R (nt,nt') g g0
         ⇒
	 ∃rhs.
         MEM (rule nt' rhs) (rules g0) ∨
         ∃l p s.
           MEM (rule l (p ++ [NTS nt'] ++ s)) (rules g0) ∨
           (nt' = startSym g0)``,

 SRW_TAC [][] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [slemma1_4, grNt2Nt'R, grNt2Nt', startSym_def,
			  rules_def] THEN
`rules g0 = MAP (ruleNt2Nt' nt nt') l` by METIS_TAC [rules_def] THEN
SRW_TAC [][] THEN
METIS_TAC [ruleNt2Nt'Mem1, ruleNt2Nt'Mem2, startSym_def , rename]);

val grNt2Nt'RSymInG' = store_thm
("grNt2Nt'RSymInG'",
``(nt ≠ nt') ⇒ (NTS nt ∈ nonTerminals g)
       ⇒
       grNt2Nt'R (nt,nt') g g0 ⇒ (NTS nt') ∈ nonTerminals g0``,

SRW_TAC [][] THEN
METIS_TAC [slemma1_4, grNt2Nt'RSymInRuleG']);


val ruleNt2Nt'Mem1' = store_thm
("ruleNt2Nt'Mem1'",
``∀l.MEM (rule ntx rhs) l ∧ (ntx ≠ nt)
 ⇒
MEM (rule ntx (MAP (rename (NTS nt) (NTS nt')) rhs)) (MAP (ruleNt2Nt' nt nt') l)``,

SRW_TAC [][ruleNt2Nt', rename] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleNt2Nt', rename] THEN
METIS_TAC [symbol_11]);

val ruleNt2Nt'Mem2' = store_thm
("ruleNt2Nt'Mem2'",
``MEM (rule l' (p ++ [NTS ntx] ++ s)) l ∧ (ntx ≠ nt) ⇒
 ∃lhs p' s'.MEM (rule lhs (p'++[NTS ntx]++s')) (MAP (ruleNt2Nt' nt nt') l)``,

SRW_TAC [][ruleNt2Nt', rename] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleNt2Nt', rename] THEN
METIS_TAC [symbol_11]);


val grNt2Nt'RNtSame = store_thm
("grNt2Nt'RNtSame",
``∀l.(nt ≠ nt') ⇒ grNt2Nt'R (nt,nt') g g0
     ⇒
    ∀e.(NTS e) ∈ (nonTerminals g) ∧ (NTS e ≠ NTS nt) ⇒ (NTS e) ∈ nonTerminals g0``,

SRW_TAC [][grNt2Nt'R] THEN
Cases_on `g` THEN SRW_TAC [][grNt2Nt'] THEN
FULL_SIMP_TAC (srw_ss()) [slemma1_4, rules_def, startSym_def] THEN
METIS_TAC [slemma1_4, ruleNt2Nt'Mem2', ruleNt2Nt'Mem1',symbol_11, rename]);


val grNt2Nt'RNtInNewg = store_thm
("grNt2Nt'RNtInNewg",
``∀l.(nt ≠ nt') ∧ grNt2Nt'R (nt,nt') g g0
     ⇒
    ∀e.(NTS e) ∈ (nonTerminals g0) ⇒ (e=nt') ∨
                                      (NTS e) ∈ nonTerminals g ∧ (e ≠ nt)``,

SRW_TAC [][grNt2Nt'R] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [slemma1_4, rules_def, startSym_def, grNt2Nt'] THEN1
(Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [ruleNt2Nt'] THEN
FULL_SIMP_TAC (srw_ss()) [rename] THEN
METIS_TAC []) THEN1
(Cases_on `e=nt'` THEN SRW_TAC [][] THEN
Cases_on `e=nt` THEN SRW_TAC [][] THEN
METIS_TAC [ruleNt2Nt'Repl, rgr_r9eq, MEM, MEM_APPEND, ruleNt2Nt'MemInOld]) THEN
FULL_SIMP_TAC (srw_ss()) [rename] THEN
Cases_on `n=nt` THEN SRW_TAC [][]);


val grNt2Nt'RNts = store_thm
("grNt2Nt'RNts",
``grNt2Nt'R (nt,nt') g g0 ⇒ (nt ≠ nt') ⇒
    NTS nt ∈ nonTerminals g
   ⇒
(nonTerminals g0 = (NTS nt') INSERT ((nonTerminals g) DELETE (NTS nt)))``,

SRW_TAC [][EQ_IMP_THM, EXTENSION] THEN1
(Cases_on `x` THEN
METIS_TAC [grNt2Nt'RNtInNewg, symbol_11, tsNotInNonTmnls]) THEN1
METIS_TAC [grNt2Nt'RSymInG'] THEN
Cases_on `x` THEN
METIS_TAC [grNt2Nt'RNtSame, slemma1_4, symbol_11, tsNotInNonTmnls]);


val grNt2Nt'RAll = store_thm
("grNt2Nt'RAll",
``∀s.FINITE s ⇒
  ∀g g''.
   (s=(nonTerminals (g:('a,'b) grammar)) ∩ (nonTerminals (g'':('a,'b) grammar))) ⇒
    INFINITE (UNIV:'a set)
         ⇒
        ∃g'.RTC (\x y.∃nt nt'.grNt2Nt'R (nt,nt') x y) g g' ∧
	    (language g = language g') ∧
            DISJOINT (nonTerminals g') (nonTerminals g'')``,

HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][] THEN1
(Q.EXISTS_TAC `g` THEN
SRW_TAC [][] THEN SRW_TAC [][DISJOINT_DEF]) THEN
`∃nt.e=NTS nt` by (Cases_on `e` THEN SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) [INSERT_DEF, EXTENSION] THEN
		   METIS_TAC [tsNotInNonTmnls]) THEN
SRW_TAC [][] THEN
`FINITE (nonTerminals g'' ∪ nonTerminals g)`
    by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET, FINITE_UNION] THEN
`∃nt'. nt' ∉ IMAGE stripNts (nonTerminals g'' ∪ nonTerminals g)`
   by METIS_TAC [NOT_IN_FINITE, IMAGE_FINITE] THEN
`∃g0. grNt2Nt'R (nt,nt') g g0` by (SRW_TAC [][grNt2Nt'R] THEN
				   FULL_SIMP_TAC (srw_ss()) [] THEN
				   METIS_TAC [stripNts]) THEN
`NTS nt' ∉  nonTerminals g` by (FULL_SIMP_TAC (srw_ss()) [INSERT_DEF, INTER_DEF,
							  EXTENSION] THEN
				METIS_TAC [symbol_11, stripNts]) THEN
`NTS nt ∈ nonTerminals g` by (FULL_SIMP_TAC (srw_ss()) [INSERT_DEF, INTER_DEF,
							EXTENSION] THEN
			      METIS_TAC [symbol_11]) THEN
`NTS nt ∈ nonTerminals g''` by (FULL_SIMP_TAC (srw_ss()) [INSERT_DEF, INTER_DEF,
							 EXTENSION] THEN
				METIS_TAC [symbol_11]) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`nt ≠ nt'` by METIS_TAC [stripNts, symbol_11] THEN
`NTS nt' ∈  nonTerminals g0` by METIS_TAC [grNt2Nt'RSymInG'] THEN
`nonTerminals g0 = NTS nt' INSERT ((nonTerminals g) DELETE (NTS nt))`
  by METIS_TAC [grNt2Nt'RNts] THEN
`(s = nonTerminals g0 ∩ nonTerminals g'')`
   by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, INTER_DEF, DELETE_DEF,
                                 INSERT_DEF] THEN
       METIS_TAC [symbol_11, stripNts]) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`g0`, `g''`] MP_TAC) THEN
ASM_REWRITE_TAC [] THEN
DISCH_THEN (Q.X_CHOOSE_THEN `g'` STRIP_ASSUME_TAC) THEN
Q.EXISTS_TAC `g'` THEN
SRW_TAC [][] THEN1
  (Q.ABBREV_TAC `r=(λx y. ∃nt nt'. grNt2Nt'R (nt,nt') x y)` THEN
   `r g g0` by (SRW_TAC [] [Abbr `r`] THEN METIS_TAC []) THEN
   METIS_TAC [RTC_RULES]) THEN
METIS_TAC [grNt2Nt'R, nt2nt'LangEq]);

val disjoint = store_thm
("disjoint",
``INFINITE (UNIV:'a set)
       ⇒
      ∃g'.(language (g:('a,'b) grammar) = language g') ∧
          DISJOINT (nonTerminals g) (nonTerminals g')``,

SRW_TAC [][] THEN
`FINITE (nonTerminals g ∩ nonTerminals g)`
 by METIS_TAC [finiteNtsList, FINITE_LIST_TO_SET, INTER_FINITE] THEN
 `∃g'.(λx y. ∃nt nt'. grNt2Nt'R (nt,nt') x y)^* g g' ∧
     (language g = language g') ∧
     DISJOINT (nonTerminals g') (nonTerminals g)` by METIS_TAC [grNt2Nt'RAll] THEN
FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
METIS_TAC [DISJOINT_INSERT]);

val INFINITE_NTS_SYMBOLS = store_thm(
  "INFINITE_NTS_SYMBOLS",
  ``INFINITE univ(:'nts) ==> INFINITE univ(:('nts,'ts)symbol)``,
  SRW_TAC [][GSYM MONO_NOT_EQ] THEN
  `IMAGE NTS univ(:'nts) ⊆ univ(:('nts,'ts)symbol)`
     by SRW_TAC [][] THEN
  `FINITE (IMAGE NTS univ(:'nts) : ('nts,'ts)symbol set)`
     by IMP_RES_TAC SUBSET_FINITE THEN
  FULL_SIMP_TAC (srw_ss()) [INJECTIVE_IMAGE_FINITE]);

val nonTerminals_grNt2Nt' = store_thm(
  "nonTerminals_grNt2Nt'",
  ``n0 ≠ n1 ⇒ NTS n0 ∉ nonTerminals (grNt2Nt' n0 n1 g)``,
  REPEAT STRIP_TAC THEN
  Cases_on `g` THEN
  FULL_SIMP_TAC (srw_ss()) [grNt2Nt', nonTerminals_def, MEM_MAP,
                            rename]
  THEN1 (POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  SRW_TAC [][] THEN
  Cases_on `y` THEN
  FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def, ruleNt2Nt', rename,
                            MEM_MAP] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN SRW_TAC [][]);

val nonTerminals_grNt2Nt'_2 = store_thm(
  "nonTerminals_grNt2Nt'_2",
  ``x ∉ nonTerminals g ∧ x ≠ NTS n1 ∧ x ≠ NTS n2 ⇒
    x ∉ nonTerminals (grNt2Nt' n1 n2 g)``,
  REPEAT STRIP_TAC THEN Cases_on `g` THEN
  FULL_SIMP_TAC (srw_ss()) [grNt2Nt', nonTerminals_def, MEM_MAP,
                            rename] THEN1
    (POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  SRW_TAC [][] THEN Cases_on `y` THEN
  FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def, ruleNt2Nt', rename,
                            MEM_MAP] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN SRW_TAC[][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `rule_nonterminals (rule n' l')` MP_TAC) THEN
  SRW_TAC [][rule_nonterminals_def] THEN
  POP_ASSUM (Q.SPEC_THEN `rule n' l'` MP_TAC) THEN
  SRW_TAC [][rule_nonterminals_def]);

val better_disjoint = store_thm(
  "better_disjoint",
  ``INFINITE univ(:'nts) ==>
    ∀s. FINITE s ==>
        ∀g : ('nts,'ts) grammar.
           ∃g'. (language g' = language g) ∧
                DISJOINT (nonTerminals g') s``,
  STRIP_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN1
    METIS_TAC [] THEN
  `∃g1. (language g1 = language g) ∧ DISJOINT (nonTerminals g1) s`
     by METIS_TAC [] THEN
  Cases_on `e ∈ nonTerminals g1` THENL [
    `∃n. NTS n ≠ e ∧ NTS n ∉ s ∧ NTS n ∉ nonTerminals g1`
       by (Q.ABBREV_TAC
             `nts = { n | NTS n ∈ s ∨ NTS n ∈ nonTerminals g1 ∨ (NTS n = e)}`
             THEN
           `FINITE (IMAGE NTS nts: ('nts,'ts) symbol set)`
              by (MATCH_MP_TAC SUBSET_FINITE_I THEN
                  Q.EXISTS_TAC `s ∪ nonTerminals g1 ∪ {e}` THEN
                  SRW_TAC [][SUBSET_DEF, Abbr`nts`, finite_nts] THEN
                  SRW_TAC [][]) THEN
           FULL_SIMP_TAC (srw_ss()) [INJECTIVE_IMAGE_FINITE] THEN
           `∃n. n ∉ nts` by METIS_TAC [NOT_IN_FINITE] THEN
           Q.EXISTS_TAC `n` THEN POP_ASSUM MP_TAC THEN
           SRW_TAC [][Abbr`nts`]) THEN
    `∃en. e = NTS en`
       by (Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [tsNotInNonTmnls]) THEN
    Q.EXISTS_TAC `grNt2Nt' en n g1` THEN
    SRW_TAC [][GSYM nt2nt'LangEq] THEN
    SRW_TAC [][DISJOINT_DEF, EXTENSION] THEN
    Cases_on `x = NTS en` THEN SRW_TAC [][nonTerminals_grNt2Nt'] THEN
    Cases_on `x ∈ s` THEN SRW_TAC [][] THEN
    `x ≠ NTS n` by METIS_TAC [] THEN
    MATCH_MP_TAC nonTerminals_grNt2Nt'_2 THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN METIS_TAC [],
    Q.EXISTS_TAC `g1` THEN SRW_TAC [][] THEN
    SRW_TAC [][ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_INSERT]
  ]);


(* Substitution *)



val substitutel = Define
    `(substitutel (e,l) [] = []) ∧
 (substitutel (e,l) (h::rst) = if (h=e) then l++substitutel (e,l) rst else
				   h::substitutel (e,l) rst)`;


val substRule = Define
`substRule (e,e') (rule l r) = rule l (substitutel (e,[e']) r)`;

val substGr = Define
`substGr (tm,gsub:('a, 'b) grammar) (g:('a, 'b) grammar) =
   G ((rules gsub) ++
      MAP (substRule (TS tm,NTS (startSym gsub))) (rules g)) (startSym g)`;

val replace = Define
`(replace [] sym (s:(β, γ) symbol list -> bool) = {[]}) ∧
 (replace ((NTS x)::rst) sym s = IMAGE (CONS (NTS x)) (replace rst sym s)) ∧
 (replace (TS t::rst) sym s =
  if t ≠ sym then IMAGE (CONS (TS t)) (replace rst sym s)
  else conc s (replace rst sym s))`;

val substlEqNil = store_thm
("substlEqNil",
``(e'≠[]) ⇒
    ((substitutel (e, e') l = []) ⇔ (l=[])) ∧
    (([] = substitutel (e,e') l) ⇔ (l=[]))``,

Cases_on `l` THEN SRW_TAC [][substitutel]);

val _ = export_rewrites ["substlEqNil"];

val subsEqNil = store_thm
("subsEqNil",
``((rule n [] = substRule (e, e') y) ⇔ (y = rule n [])) ∧
  ((substRule (e,e') y = rule n []) ⇔ (y=rule n []))``,

Cases_on `y` THEN
SRW_TAC [][substRule] THEN
METIS_TAC []);

val _ = export_rewrites ["subsEqNil"];


val ruleNilsbg = store_thm
("ruleNilsbg",
``MEM (rule n []) (rules (substGr (sym,gsub) g)) ∧
NTS n ∈ nonTerminals g ∧ DISJOINT (nonTerminals g) (nonTerminals gsub) ⇒
MEM (rule n []) (rules g)``,

SRW_TAC [][substGr, rules_def]
THENL[
      FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
      METIS_TAC [slemma1_4],

      FULL_SIMP_TAC (srw_ss()) [MEM_MAP]]);




val substTwice = store_thm
("substTwice",
``∀l.¬MEM n l ⇒ (substitutel (n, [t]) (substitutel (t,[n]) l) = l)``,
Induct_on `l` THEN SRW_TAC [][substitutel]);

val IS_SUFFIX_CONS2_E = store_thm
("IS_SUFFIX_CONS2_E",
``IS_SUFFIX s (h::t) ⇒ IS_SUFFIX s t``,

SRW_TAC [][IS_SUFFIX_APPEND]  THEN
METIS_TAC [APPEND, APPEND_ASSOC]);


val notMemsbl = store_thm
("notMemsbl",
``∀l.¬MEM (TS sym) (substitutel (TS sym,[NTS (startSym gsub)]) l)``,

Induct_on `l` THEN SRW_TAC [][substitutel]);

val notMemSymsbg = store_thm
("notMemSymsbg",
``MEM (rule n l) (rules (substGr (sym,gsub) g)) ∧ (NTS n ∈ nonTerminals g) ∧
DISJOINT (nonTerminals g) (nonTerminals gsub) ⇒
¬MEM (TS sym) l``,

SRW_TAC [][substGr, rules_def] THEN1
(FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
METIS_TAC [slemma1_4]) THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [substRule] THEN
SRW_TAC [][] THEN
METIS_TAC [notMemsbl]);


val isSfxMem = store_thm
("isSfxMem",
``∀ptl l.IS_SUFFIX ptl l ⇒ (∀e.MEM e l ⇒ MEM e ptl)``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [IS_SUFFIX_APPEND]);


val sbl1Mem = store_thm
("sbl1Mem",
``∀l.MEM x (substitutel (e, [e']) l) ⇒ (x=e') ∨ MEM x l``,

Induct_on `l` THEN SRW_TAC [][substitutel] THEN
METIS_TAC []);

val sbgNtsIng = store_thm
("sbgNtsIng",
``DISJOINT (nonTerminals g) (nonTerminals gsub) ∧
  (NTS n ∈ nonTerminals g) ∧ MEM (rule n rhs) (rules (substGr (sym,gsub) g))
			⇒
(∀e.MEM (NTS e) rhs ⇒ (e=startSym gsub) ∨ (NTS e ∈ nonTerminals g))``,


SRW_TAC [][substGr, rules_def] THEN1
(FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
 METIS_TAC [slemma1_4]) THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [substRule] THEN
SRW_TAC [][] THEN
METIS_TAC [sbl1Mem, slemma1_4, rgr_r9eq, symbol_11]);


val replaceApp = store_thm
("replaceApp",
``∀l1 l2 l1' l2'.
 l1' ∈ replace l1 sym s ∧ l2' ∈ replace l2 sym s
⇒
(l1'++l2') ∈ replace (l1++l2) sym s``,

Induct_on `l1` THEN SRW_TAC [][replace] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [replace] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [conc_def] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND_ASSOC]);


val memRulegsub = store_thm
("memRulegsub",
``DISJOINT (nonTerminals g) (nonTerminals gsub) ⇒
 (NTS n) ∈ nonTerminals gsub ⇒
 MEM (rule n l) (rules (substGr (sym,gsub) g)) ⇒
 MEM (rule n l) (rules gsub)``,

SRW_TAC [][substGr, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [substRule] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
METIS_TAC [slemma1_4]);


val memGetSyms = store_thm
("memGetSyms",
``∀l.MEM (Node n' ts) l ⇒ MEM (NTS n') (getSymbols l)``,

Induct_on `l` THEN SRW_TAC [][getSymbols_def] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols_def] THEN
(Cases_on `h'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols_def]));

val vptgsubInLang = store_thm
("vptgsubInLang",
``∀g' t.validptree g' t ⇒ (g'=substGr (sym,gsub) g) ⇒
DISJOINT (nonTerminals g) (nonTerminals gsub) ⇒
(root t) ∈ nonTerminals gsub ⇒
(derives gsub)^* [root t] (MAP TS (fringe t))``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [root_def, validptree] THEN
`MEM (rule n (getSymbols ptl)) (rules gsub)` by METIS_TAC [memRulegsub] THEN
 `∀e.MEM e ptl ∧ isNode e ⇒  root e ∈ nonTerminals gsub`
 by (SRW_TAC [][] THEN
     Cases_on `e` THEN
     FULL_SIMP_TAC (srw_ss()) [isNode_def, root_def] THEN
     SRW_TAC [][slemma1_4] THEN
     `MEM (NTS n') (getSymbols ptl)` by METIS_TAC [memGetSyms] THEN
     METIS_TAC [rgr_r9eq]) THEN
`∀t. MEM t ptl ⇒ (derives gsub)^* [root t] (MAP TS (fringe t))`
 by (SRW_TAC [][] THEN
     Cases_on `t` THEN
     FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [fringe_def, root_def] THEN
     RES_TAC THEN
     FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [fringe_def, root_def, isNode_def]) THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
`(derives gsub)^* [NTS n] (MAP TS (FLAT (MAP fringe ptl)))`
by METIS_TAC [getSymsEqRoot, ptlRtcd, res1, RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [getSymbols_def, fringe_def]);


val vptSbgrImpGr = store_thm
("vptSbgrImpGr",
``∀g t.validptree (substGr (sym,gsub:('a, 'b) grammar) (g:('a, 'b) grammar)) t ∧
   (root t) ∈ nonTerminals g ∧ DISJOINT (nonTerminals g) (nonTerminals gsub)
   ⇒
   ∃t' (w:('a, 'b) symbol list).
   (MAP TS (fringe t') = w) ∧
   (MAP TS (fringe t)) ∈ (replace w sym (language gsub)) ∧
   validptree g t' ∧ (root t' = root t)``,

HO_MATCH_MP_TAC validptree_ind THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [validptree, root_def, fringe_def] THEN

Q.ABBREV_TAC `fr:('a,'b) symbol list = MAP TS (FLAT (MAP fringe ptl))` THEN
Q_TAC SUFF_TAC
`∃ts. fr ∈ replace (MAP TS (FLAT (MAP  fringe ts))) sym (language gsub) ∧
   (∀t.MEM t ts ∧ isNode t ⇒ validptree g t) ∧
   (getSymbols ts = substitutel (NTS (startSym gsub), [TS sym]) (getSymbols ptl))`
THENL[
      SRW_TAC [][Abbr `fr`] THEN
      Q.EXISTS_TAC `Node n ts` THEN
      SRW_TAC [boolSimps.ETA_ss][root_def, validptree, fringe_def] THEN
      FULL_SIMP_TAC (srw_ss()) [substGr, rules_def] THEN1
      (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
       METIS_TAC [slemma1_4]) THEN
      FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
      Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [substRule] THEN
      `¬MEM (NTS (startSym gsub)) l` by
      (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
       METIS_TAC [slemma1_4, rgr_r9eq]) THEN
      SRW_TAC [][substTwice],

      `¬MEM (TS sym) (getSymbols ptl)`
      by METIS_TAC [notMemSymsbg] THEN
      Q.PAT_ASSUM `¬MEM e l` MP_TAC THEN
      markerLib.UNABBREV_ALL_TAC THEN
      SRW_TAC [][] THEN
      markerLib.UNABBREV_ALL_TAC THEN
      Q_TAC SUFF_TAC `∀ptl'.IS_SUFFIX ptl ptl' ⇒
      ∃ts.
      MAP TS (FLAT (MAP fringe ptl')) ∈
      replace (MAP TS (FLAT (MAP fringe ts))) sym
        (language gsub) ∧
	(∀t. MEM t ts ∧ isNode t ⇒ validptree g t) ∧
      (getSymbols ts =
       substitutel (NTS (startSym gsub),[TS sym])
         (getSymbols ptl'))` THEN1

      (SRW_TAC [][] THEN
      POP_ASSUM MATCH_MP_TAC THEN
      SRW_TAC [][GSYM IS_PREFIX_REVERSE, IS_PREFIX_REFL]) THEN

      Induct_on `ptl'` THEN SRW_TAC [][] THEN1
      (Q.EXISTS_TAC `[]` THEN
       FULL_SIMP_TAC (srw_ss()) [IS_SUFFIX, replace, getSymbols_def]) THEN

      IMP_RES_TAC IS_SUFFIX_CONS2_E THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `h`
      THENL[
	    SRW_TAC [][fringe_def, getSymbols_def] THEN
	    Cases_on `t=sym` THEN SRW_TAC [][] THEN1
	    `MEM (TS sym) (getSymbols ptl)`
	    by (`MEM (Leaf sym) ptl` by METIS_TAC [isSfxMem, MEM] THEN
		FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
		METIS_TAC [getSyms_append, getSymbols_def]) THEN
	    Q.EXISTS_TAC `Leaf t::ts` THEN
	    SRW_TAC [][fringe_def]
	    THENL[
		  SRW_TAC [][replace],
		  FULL_SIMP_TAC (srw_ss()) [isNode_def],
		  FULL_SIMP_TAC (srw_ss()) [],
		  Cases_on `ts` THEN SRW_TAC [][getSymbols_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [substitutel]
		  ],

	    SRW_TAC [boolSimps.ETA_ss][fringe_def]  THEN
	    Cases_on `n'=startSym gsub`
	    THENL[
		  SRW_TAC [][] THEN
		  Q.EXISTS_TAC `Leaf sym::ts` THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [isNode_def]
		  THENL[
			SRW_TAC [][fringe_def, replace] THEN
			SRW_TAC [][conc_def] THEN
			Q.EXISTS_TAC `MAP TS (fringe (Node (startSym gsub) l))` THEN
			Q.EXISTS_TAC `MAP TS (FLAT (MAP fringe ptl'))` THEN
			SRW_TAC [][]
			THENL[
			      SRW_TAC [boolSimps.ETA_ss][fringe_def] THEN
			      `MEM (Node (startSym gsub) l) ptl`
			      by METIS_TAC [isSfxMem, MEM] THEN
			      `validptree (substGr (sym,gsub) g)
			      (Node (startSym gsub) l)`
			      by METIS_TAC [isNode_def] THEN
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      SRW_TAC [][fringe_def] THEN
			      `NTS (startSym gsub) ∈ nonTerminals gsub`
			      by (Cases_on `gsub` THEN
				  SRW_TAC [][nonTerminals_def,startSym_def]) THEN
			      `(derives gsub)^* [NTS (startSym gsub)]
			      (MAP TS (fringe (Node (startSym gsub) l)))`
			      by METIS_TAC [vptgsubInLang, root_def] THEN
			      FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss)
			      [language_def,fringe_def] THEN
			      METIS_TAC [everyTmMapTs],
			      SRW_TAC [boolSimps.ETA_ss][fringe_def]],

			      Cases_on `ts` THEN SRW_TAC [][getSymbols_def] THEN
			      FULL_SIMP_TAC (srw_ss()) [substitutel]
			      ],

			`MEM (NTS n') (getSymbols ptl)`
			by (`MEM (Node n' l) ptl` by METIS_TAC [isSfxMem, MEM] THEN
			    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
			    METIS_TAC [getSyms_append, getSymbols_def,
				       APPEND_ASSOC,APPEND,
				       symbol_11]) THEN
			`root (Node n' l) ∈ nonTerminals g`
			by METIS_TAC [sbgNtsIng, symbol_11, root_def] THEN
			`MEM (Node n' l) ptl` by METIS_TAC [isSfxMem, MEM] THEN
			`EVERY (isTmnlSym:('a, 'b) symbol -> bool)
            		  (MAP TS (fringe (Node n' l)))`
			by METIS_TAC [everyTmMapTs] THEN
			`∃t'. MAP TS (fringe (Node n' l)) ∈
			replace (MAP TS (fringe t')) sym
			(language gsub) ∧ validptree g t' ∧
			(root t' = root (Node n' l))`
			by METIS_TAC [isNode_def] THEN
			Q.EXISTS_TAC `t'::ts` THEN
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) []
			THENL[
			      FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss)
			      [fringe_def] THEN
			      METIS_TAC [replaceApp],

			      FULL_SIMP_TAC (srw_ss()) [root_def] THEN
			      Cases_on `t'` THEN
			      FULL_SIMP_TAC (srw_ss()) [root_def] THEN
			      SRW_TAC [][] THEN
			      Cases_on `ts` THEN SRW_TAC [][getSymbols_def] THEN
			      FULL_SIMP_TAC (srw_ss()) [substitutel]
			      ]
			]]]);


val sbSSymEq = store_thm
("sbSSymEq",
``(startSym g = startSym (substGr (tm,gsub) g))``,

Cases_on `g` THEN
SRW_TAC [][substGr,startSym_def]);

(*
STEP 1
(derives g)^* [NTS (startSym g)] w ⇒
(derives (substGr (tm,gsub) g))^*
[NTS (startSym (substGr (tm,gsub) g))]
(substitutel (tm,[NTS (startSym (substGr (tm,gsub) g))]) w)
*)

val sb1 = store_thm
("sb1",
``isTmnlSym tm ⇒
 (substitutel (tm,l') [NTS s] = [NTS s])``,

Cases_on `tm` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,substitutel]);

val sblAppend = store_thm
("sblAppend",
``∀w1 w2.
 substitutel (tm,l) (w1++w2) = substitutel (tm,l) w1 ++ substitutel (tm,l) w2``,

Induct_on `w1` THEN Induct_on `w2` THEN SRW_TAC [][substitutel]);

val sblRuleMemMapsbr = store_thm
("sblRuleMemMapsbr",
``∀l.MEM (rule lhs rhs) l
 ⇒
MEM (rule lhs (substitutel (tm,[NTS n]) rhs))
(MAP (substRule (tm,NTS n)) l)``,

SRW_TAC [][rgr_r9eq] THEN
SRW_TAC [][MAP_APPEND, substRule] THEN
METIS_TAC []);

val memRuleInsbg = store_thm
("memRuleInsbg",
``MEM (rule lhs rhs) (rules g)
 ⇒
 MEM (rule lhs (substitutel (TS tm,[NTS (startSym gsub)]) rhs))
(rules (substGr (tm,gsub) g))``,

SRW_TAC [][substGr] THEN
Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,startSym_def] THEN
METIS_TAC [sblRuleMemMapsbr]);


val derivgImpsbg = store_thm
("derivgImpsbg",
``derives g w w' ⇒
derives (substGr (tm,gsub) g)
(substitutel (TS tm,[NTS (startSym gsub)]) w)
(substitutel (TS tm,[NTS (startSym gsub)]) w')``,

SRW_TAC [][derives_def] THEN
SRW_TAC [][sblAppend] THEN
Q.EXISTS_TAC `substitutel (TS tm,[NTS (startSym gsub)]) s1` THEN
Q.EXISTS_TAC `substitutel (TS tm,[NTS (startSym gsub)]) s2` THEN
Q.EXISTS_TAC `substitutel (TS tm,[NTS (startSym gsub)]) rhs` THEN
Q.EXISTS_TAC `lhs` THEN
SRW_TAC [][substitutel] THEN
SRW_TAC [][] THEN
METIS_TAC [sb1,symbol_11,sbSSymEq,memRuleInsbg]);



val grSSymRtcdSubs = store_thm
("grSSymRtcdSubs",
``∀s w.(derives g)^* s w ⇒ (s = [NTS (startSym g)]) ⇒
 (derives (substGr (tm,gsub) g))^*
 [NTS (startSym g)] (substitutel (TS tm,[NTS (startSym gsub)]) w)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [][] THEN
SRW_TAC [][substitutel] THEN
METIS_TAC [sb1, RTC_RULES_RIGHT1, symbol_11,sbSSymEq, derivgImpsbg]);



(*
STEP 2
(derives (substGr (tm,gsub) g))^*
(substitutel (tm,[NTS (startSym (substGr (tm,gsub) g))]) w)
(replaced (w,tm,language gsub) w')
*)


val gsubDerives = store_thm
("gsubDerives",
``derives gsub x y ⇒ (derives (substGr (tm,gsub) g)) x y``,

SRW_TAC [][derives_def, substGr, rules_def] THEN
METIS_TAC [sblRuleMemMapsbr]);

val gsubRtcd = store_thm
("gsubRtcd",
``∀x y.(derives gsub)^* x y ⇒ (derives (substGr (tm,gsub) g))^* x y``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES, gsubDerives]);


val sblImprepl = store_thm
("sblImprepl",
``∀w w'. w' ∈ replace w tm (language gsub) ⇒
(derives (substGr (tm,gsub) g))^*
(substitutel (TS tm,[NTS (startSym gsub)]) w) w'``,

Induct_on `w` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [replace, substitutel] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [replace] THEN
SRW_TAC [][] THEN1
METIS_TAC [rtc_derives_same_append_left, APPEND] THEN1
(FULL_SIMP_TAC (srw_ss()) [conc_def] THEN
SRW_TAC [][] THEN
`(derives gsub)^* [NTS (startSym gsub)] u` by
 FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN
`(derives (substGr (t,gsub) g))^* [NTS (startSym gsub)] u`
by METIS_TAC [gsubRtcd] THEN
METIS_TAC [APPEND, derives_append]) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC [rtc_derives_same_append_left, APPEND]);


val replTmnls = store_thm
("replTmnls",
``∀w w'.EVERY isTmnlSym w ⇒ w' ∈ replace w tm (language g) ⇒
 EVERY isTmnlSym w'``,

Induct_on `w` THEN SRW_TAC [][replace] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, replace] THEN
Cases_on `t=tm` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [conc_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [language_def, isTmnlSym_def]);

val grImpSubst = store_thm
("grImpSubst",
``DISJOINT (nonTerminals g) (nonTerminals gsub) ∧
 w ∈ language (g:('a, 'b) grammar) ∧
 w' ∈ replace w tm (language gsub)
 ⇒
 w' ∈ language (substGr (tm,gsub) g)``,

SRW_TAC [][] THEN
IMP_RES_TAC sblImprepl THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`g`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [language_def,EXTENSION] THEN
SRW_TAC [][] THEN1
METIS_TAC [RTC_RTC, grSSymRtcdSubs, sbSSymEq] THEN
METIS_TAC [replTmnls, language_def]);


val substImpGr = store_thm
("substImpGr",
``DISJOINT (nonTerminals g) (nonTerminals gsub) ∧
  w' ∈ language (substGr (tm,gsub) g)
 ⇒
∃w. w ∈ language g ∧ w' ∈ replace w tm (language gsub)``,

SRW_TAC [][ptLangThm] THEN
SRW_TAC [][] THEN
`root t ∈ nonTerminals g`
 by (Cases_on `g` THEN
     FULL_SIMP_TAC (srw_ss()) [nonTerminals_def, substGr, startSym_def]) THEN
`∃t' w.(MAP TS (fringe t') = w) ∧
 MAP TS (fringe t) ∈ replace w tm (language gsub) ∧ validptree g t' ∧
 (root t' = root t)`
by METIS_TAC [vptSbgrImpGr] THEN
Q.EXISTS_TAC `w` THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `t'` THEN
SRW_TAC [][sbSSymEq]);



val substThm = store_thm
("substThm",
 ``DISJOINT (nonTerminals g) (nonTerminals gsub) ⇒
(w' ∈ language (substGr (tm,gsub) g) =
 ∃w. w ∈ language g ∧ w' ∈ replace w tm (language gsub))``,

SRW_TAC [][EQ_IMP_THM] THEN
 METIS_TAC [grImpSubst, substImpGr]);


(* Theorem 6.1
CFLs are closed under union, concatenation and Kleene closure.
*)

val grUnion = Define
`grUnion s0 g1 g2 =
    G (rules g1++rules g2++[rule s0 [NTS (startSym g1)]]++
       [rule s0 [NTS (startSym g2)]]) s0`;

val gruRtcSsg1 = store_thm
("gruRtcSsg1",
``(derives (grUnion s0 g1 g2))^* [NTS s0] [NTS (startSym g1)]``,
MATCH_MP_TAC RTC_SUBSET THEN
SRW_TAC [][derives_def, rules_def, grUnion] THEN
METIS_TAC [APPEND_NIL]);

val gruRtcSsg2 = store_thm
("gruRtcSsg2",
``(derives (grUnion s0 g1 g2))^* [NTS s0] [NTS (startSym g2)]``,
MATCH_MP_TAC RTC_SUBSET THEN
SRW_TAC [][derives_def, rules_def, grUnion] THEN
METIS_TAC [APPEND_NIL]);

val gruDerivFrmg1 = store_thm
("gruDerivFrmg1",
``derives g1 w w' ⇒
 (derives (grUnion s0 g1 g2)) w w'``,

SRW_TAC [][grUnion, derives_def, rules_def] THEN
METIS_TAC [MEM_APPEND, APPEND_NIL]);

val gruDerivFrmg2 = store_thm
("gruDerivFrmg2",
``derives g2 w w' ⇒
 (derives (grUnion s0 g1 g2)) w w'``,

SRW_TAC [][grUnion, derives_def, rules_def] THEN
METIS_TAC [MEM_APPEND, APPEND_NIL]);

val gruDerivFrmg1 = store_thm
("gruDerivFrmg1",
``∀w w'.(derives g1)^* w w' ⇒
 (derives (grUnion s0 g1 g2))^* w w'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [gruDerivFrmg1, RTC_RULES]);

val gruDerivFrmg2 = store_thm
("gruDerivFrmg2",
``∀w w'.(derives g2)^* w w' ⇒
 (derives (grUnion s0 g1 g2))^* w w'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [gruDerivFrmg2, RTC_RULES]);

val gruStartRuleRhs = store_thm
("gruStartRuleRhs",
``MEM (rule lhs rhs) (rules (grUnion lhs g1 g2)) ∧
  (NTS lhs) ∉ (nonTerminals g1 ∪ nonTerminals g2)
      ⇒
   (rhs = [NTS (startSym g1)]) ∨ (rhs = [NTS (startSym g2)])``,

SRW_TAC [] [grUnion, rules_def] THEN
METIS_TAC [slemma1_4]);


val gruRtcDerivgNt = store_thm
("gruRtcDerivgNt",
``∀w w'.(derives g)^* w w' ⇒ (¬MEM (NTS nt) w) ⇒ (NTS nt) ∉ nonTerminals g
             ⇒
	  ¬ (MEM (NTS nt) w')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
Q_TAC SUFF_TAC `¬MEM (NTS nt) w'` THEN1
METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [slemma1_4, rgr_r9eq]);


val ruleg2NoDerivg1 = store_thm
("ruleg2NoDerivg1",
``∀g1 g2.DISJOINT (nonTerminals g1) (nonTerminals g2) ∧
       MEM (rule lhs rhs) (rules g2) ∧ (NTS nt ≠ NTS lhs)
          ⇒
       ¬(derives g1)^* [NTS nt] (pfx++[NTS lhs]++sfx)``,

SPOSE_NOT_THEN ASSUME_TAC THEN
SRW_TAC [][] THEN
`[NTS nt] ≠ pfx++[NTS lhs]++sfx` by (Cases_on `pfx` THEN SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, INTER_DEF, EXTENSION] THEN
`LENGTH (pfx++[NTS lhs]++sfx) ≥ 1`
 by FULL_SIMP_TAC (arith_ss) [LENGTH_APPEND, LENGTH] THEN
METIS_TAC [slemma1_4, MEM, MEM_APPEND, rtcDerivesInRuleRhs']);

val ruleg1NoDerivg2 = store_thm
("ruleg1NoDerivg2",
``∀g1 g2.DISJOINT (nonTerminals g1) (nonTerminals g2) ∧
       MEM (rule lhs rhs) (rules g1) ∧ (NTS nt ≠ NTS lhs)
       ⇒
       ¬(derives g2)^* [NTS nt] (pfx++[NTS lhs]++sfx)``,

SPOSE_NOT_THEN ASSUME_TAC THEN
SRW_TAC [][] THEN
`[NTS nt] ≠ pfx++[NTS lhs]++sfx` by (Cases_on `pfx` THEN SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, INTER_DEF, EXTENSION] THEN
`LENGTH (pfx++[NTS lhs]++sfx) ≥ 1`
 by FULL_SIMP_TAC (arith_ss) [LENGTH_APPEND, LENGTH] THEN
METIS_TAC [slemma1_4, MEM, MEM_APPEND, rtcDerivesInRuleRhs']);



val gruNtNotInRhs = store_thm
("gruNtNotInRhs",
``(NTS nt) ∉ (nonTerminals g1 ∪ nonTerminals g2)
     ⇒
     ¬∃lhs p s. MEM (rule lhs (p ++ [NTS nt] ++ s))
                         (rules (grUnion nt g1 g2))``,

SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [grUnion, rules_def] THEN
METIS_TAC [slemma1_4, lreseq]);


val gruLdNtRtcDNt = store_thm
("gruLdNtRtcDNt",
``(NTS nt) ∉ (nonTerminals g1 ∪ nonTerminals g2) ∧
   (derives (grUnion nt g1 g2))^* [NTS nt] (s1++[NTS nt]++s2)
                   ⇒
		 (s1=[]) ∧ (s2=[])``,

Cases_on `[NTS nt] = s1++[NTS nt]++s2` THEN1
METIS_TAC [lreseq] THEN
METIS_TAC [gruNtNotInRhs, rtcDerivesInRuleRhs']);


val gruNtRtcDNt = store_thm
("gruNtRtcDNt",
``(NTS nt) ∉ (nonTerminals g1 ∪ nonTerminals g2) ∧
 (derives (grUnion nt g1 g2))^* [NTS nt] (s1 ++ [NTS nt] ++ s2)
         ⇒
      (s1=[]) ∧ (s2=[])``,

METIS_TAC [rtc2list_exists', gruLdNtRtcDNt]);


val gruRtcDeriv = store_thm
("gruRtcDeriv",
``∀w w'.(derives (grUnion s0 g1 g2))^* w w' ⇒ (w=[NTS s0]) ⇒
        (NTS s0) ∉ (nonTerminals g1 ∪ nonTerminals g2) ⇒
	DISJOINT (nonTerminals g1) (nonTerminals g2)
            ⇒
            ((w=w') ∨ (derives g1)^* [NTS (startSym g1)] w' ∨
	     (derives g2)^* [NTS (startSym g2)] w')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
`([NTS s0] = w') ∨
          (derives g1)^* [NTS (startSym g1)] w' ∨
          (derives g2)^* [NTS (startSym g2)] w'` by METIS_TAC [] THEN
SRW_TAC [][] THEN1
 (FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
  SRW_TAC [][] THEN
  METIS_TAC [gruStartRuleRhs, RTC_REFL, IN_UNION])
THENL[
      Cases_on `[NTS s0]=w'`
      THENL[
	FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES2] THEN1
	METIS_TAC [slemma1_4] THEN
	FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
	SRW_TAC [][] THEN
	`¬(MEM (NTS lhs) [NTS (startSym g1)])`  by (SRW_TAC [][] THEN
						    METIS_TAC [slemma1_4]) THEN
	`(derives g1)^* [NTS (startSym g1)] [NTS lhs]`
	by METIS_TAC [RTC_RULES_RIGHT1] THEN
	IMP_RES_TAC gruRtcDerivgNt THEN
	FIRST_X_ASSUM (Q.SPECL_THEN [`lhs`] MP_TAC) THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [],

	FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	SRW_TAC [][] THEN
	`(rules (grUnion s0 g1 g2)) = (rules g1 ++ rules g2 ++
				       [rule s0 [NTS (startSym g1)]] ++
				       [rule s0 [NTS (startSym g2)]])` by METIS_TAC [grUnion, rules_def] THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN1
	(`NTS s0 ≠ NTS lhs` by METIS_TAC [slemma1_4] THEN
	METIS_TAC [res1, derives_same_append_left, derives_same_append_right,
		   RTC_RULES_RIGHT1, ruleg2NoDerivg1, ruleg1NoDerivg2]) THEN1
	(`NTS (startSym g1) ≠ NTS lhs` by (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, INTER_DEF, EXTENSION] THEN
					   METIS_TAC [slemma1_4]) THEN
	METIS_TAC [ruleg2NoDerivg1, ruleg1NoDerivg2]) THEN
	(SRW_TAC [][] THEN
	(`(s1=[]) ∧ (s2=[])` by METIS_TAC [gruNtRtcDNt, IN_UNION] THEN
	 SRW_TAC [][]))
	],

      Cases_on `[NTS s0]=w'`
      THENL[
	FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES2] THEN1
	(SRW_TAC [][] THEN
	METIS_TAC [slemma1_4]) THEN
	FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
	SRW_TAC [][] THEN
	`¬(MEM (NTS s0) [NTS (startSym g2)])`  by (SRW_TAC [][] THEN
						    METIS_TAC [slemma1_4]) THEN
	`(derives g2)^* [NTS (startSym g2)] [NTS s0]`
	by METIS_TAC [RTC_RULES_RIGHT1] THEN
	IMP_RES_TAC gruRtcDerivgNt THEN
	FIRST_X_ASSUM (Q.SPECL_THEN [`s0`] MP_TAC) THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [],

	FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
	SRW_TAC [][] THEN
	`(rules (grUnion s0 g1 g2)) = (rules g1 ++ rules g2 ++
				       [rule s0 [NTS (startSym g1)]] ++
				       [rule s0 [NTS (startSym g2)]])` by METIS_TAC [grUnion, rules_def] THEN
	FULL_SIMP_TAC (srw_ss()) [] THEN1
	(`NTS (startSym g2) ≠ NTS lhs` by (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, INTER_DEF, EXTENSION] THEN
					   METIS_TAC [slemma1_4]) THEN
	 METIS_TAC [res1, derives_same_append_left, derives_same_append_right,
		   RTC_RULES_RIGHT1, ruleg2NoDerivg1, ruleg1NoDerivg2]) THEN1
	 METIS_TAC [res1, derives_same_append_left, derives_same_append_right,
		   RTC_RULES_RIGHT1, ruleg2NoDerivg1, ruleg1NoDerivg2] THEN
	(SRW_TAC [][] THEN
	(`(s1=[]) ∧ (s2=[])` by METIS_TAC [gruNtRtcDNt, IN_UNION] THEN
	 SRW_TAC [][]))
	]]);

val startSym_grUnion = store_thm(
  "startSym_grUnion",
  ``startSym (grUnion s0 g1 g2) = s0``,
  SRW_TAC [][grUnion, startSym_def])

val gruRtcDeriv' = SIMP_RULE (srw_ss()) [AND_IMP_INTRO] gruRtcDeriv

val union_cfg = store_thm(
  "union_cfg",
  ``∀g1 g2. INFINITE univ(:'nts) ⇒
            ∃g. language (g:('nts,'ts)grammar) = language g1 ∪ language g2``,
  REPEAT STRIP_TAC THEN
  `∃g2'. (language g2 = language g2') ∧
         DISJOINT (nonTerminals g2') (nonTerminals g1)`
      by METIS_TAC [better_disjoint, finite_nts] THEN
  `∃s0. s0 ∉ IMAGE stripNts (nonTerminals g1 ∪ nonTerminals g2')`
      by METIS_TAC [NOT_IN_FINITE, IMAGE_FINITE, FINITE_UNION, finite_nts] THEN
  `NTS s0 ∉ nonTerminals g1 ∪ nonTerminals g2'`
     by (FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [stripNts]) THEN
  Q.EXISTS_TAC `grUnion s0 g1 g2'` THEN
  ASM_SIMP_TAC (srw_ss()) [language_def, EXTENSION, startSym_grUnion] THEN
  Q.X_GEN_TAC `w` THEN Cases_on `isWord w` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  `∀n. w ≠ [NTS n]`
     by (REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
  SRW_TAC [][EQ_IMP_THM] THENL [
    METIS_TAC [gruRtcDeriv, DISJOINT_SYM, IN_UNION],
    METIS_TAC [RTC_RTC, gruDerivFrmg1, gruRtcSsg1],
    METIS_TAC [RTC_RTC, gruDerivFrmg2, gruRtcSsg2]
  ]);

val grConcat = Define
`grConcat s0 g1 g2 =
    G (rules g1++rules g2++[rule s0 [NTS (startSym g1);NTS (startSym g2)]]) s0`;

val grcRtcDTog1 = store_thm
("grcRtcDTog1",
``∀w w'.(derives g1)^* w w' ⇒ (derives (grConcat s0 g1 g2))^* w w'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
`MEM (rule lhs rhs) (rules (grConcat s0 g1 g2))` by METIS_TAC [grConcat, rules_def,
							       MEM_APPEND] THEN
METIS_TAC [res1, RTC_RULES, derives_same_append_right, derives_same_append_left]);


val grcRtcDTog2 = store_thm
("grcRtcDTog2",
``∀w w'.(derives g2)^* w w' ⇒ (derives (grConcat s0 g1 g2))^* w w'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
`MEM (rule lhs rhs) (rules (grConcat s0 g1 g2))` by METIS_TAC [grConcat, rules_def,
							       MEM_APPEND] THEN
METIS_TAC [res1, RTC_RULES, derives_same_append_right, derives_same_append_left]);


val grcStartRule = store_thm
("grcStartRule",
``derives (grConcat s0 g1 g2) [NTS s0]
      [NTS (startSym g1);NTS(startSym g2)]`` ,

METIS_TAC [grConcat,MEM, MEM_APPEND,startSym_def, rules_def, res1]);

val grcStartRuleRhs = store_thm
("grcStartRuleRhs",
``MEM (rule lhs rhs) (rules (grConcat lhs g1 g2)) ∧
  (NTS lhs) ∉ (nonTerminals g1 ∪ nonTerminals g2)
      ⇒
   (rhs = [NTS (startSym g1);NTS (startSym g2)])``,

SRW_TAC [] [grConcat, rules_def] THEN
METIS_TAC [slemma1_4]);


val grcDerivImpg1g2 = store_thm
("grcDerivImpg1g2",
``DISJOINT (nonTerminals g1) (nonTerminals g2) ∧
(NTS s0) ∉ (nonTerminals g1 ∪ nonTerminals g2) ∧
(derives g1)^* [NTS (startSym g1)] u ∧ (derives g2)^* [NTS (startSym g2)] v ∧
derives (grConcat s0 g1 g2) (u ++ v) w''
      ⇒
∃u' v'.(w''=u'++v) ∧ derives g1 u u'  ∨
∃u' v'.(w''=u++v') ∧ derives g2 v v'``,

SRW_TAC [][derives_def] THEN
`MEM (rule lhs rhs) (rules g1 ++ rules g2 ++
[rule s0 [NTS (startSym g1); NTS (startSym g2)]])` by METIS_TAC [rules_def, grConcat] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃l1 l2.
      (u = s1 ++ [NTS lhs] ++ l1) ∧ (v = l2) ∧
      (s2 = l1 ++ l2) ∨
      (v = l2 ++ [NTS lhs] ++ s2) ∧ (u = l1) ∧
      (s1 = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, INTER_DEF, EXTENSION]
THENL[

      METIS_TAC [APPEND, APPEND_ASSOC],

      `[NTS (startSym g2)] ≠ (l2 ++ [NTS lhs] ++ s2)` by
      (Cases_on `l2` THEN SRW_TAC [][] THEN
       METIS_TAC [slemma1_4]) THEN
      METIS_TAC [slemma1_4, rtcDerivesInRuleRhs'],

      `[NTS (startSym g1)] ≠ (s1 ++ [NTS lhs] ++ l1)` by
      (Cases_on `s1` THEN SRW_TAC [][] THEN
       METIS_TAC [slemma1_4]) THEN
      METIS_TAC [slemma1_4, rtcDerivesInRuleRhs'],

      METIS_TAC [APPEND, APPEND_ASSOC],

      `[NTS (startSym g1)] ≠ (s1 ++ [NTS lhs] ++ l1)` by
      (Cases_on `s1` THEN SRW_TAC [][] THEN
       METIS_TAC [slemma1_4]) THEN
      METIS_TAC [slemma1_4, rtcDerivesInRuleRhs'],

      `[NTS (startSym g2)] ≠ (l2 ++ [NTS lhs] ++ s2)` by
      (Cases_on `l2` THEN SRW_TAC [][] THEN
       METIS_TAC [slemma1_4]) THEN
      METIS_TAC [slemma1_4, rtcDerivesInRuleRhs']
      ]);



val grcRtcDeriv = store_thm
("grcRtcDeriv",
``∀w w'.(derives (grConcat s0 g1 g2))^* w w' ⇒ (w=[NTS s0]) ⇒
        (NTS s0) ∉ (nonTerminals g1 ∪ nonTerminals g2) ⇒
	DISJOINT (nonTerminals g1) (nonTerminals g2)
            ⇒
            ((w=w') ∨ ∃u v.(w'=u++v) ∧ (derives g1)^* [NTS (startSym g1)] u ∧
	     (derives g2)^* [NTS (startSym g2)] v)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [][] THEN
Cases_on `w'=[NTS s0]` THEN SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
      `(w'' = [NTS (startSym g1); NTS (startSym g2)])`
      by METIS_TAC [grcStartRuleRhs, IN_UNION] THEN
      DISJ2_TAC THEN
      METIS_TAC [RTC_RULES, APPEND],

      `∃u v.(w' = u ++ v) ∧
            (derives g1)^* [NTS (startSym g1)] u ∧
            (derives g2)^* [NTS (startSym g2)] v` by METIS_TAC [] THEN
      SRW_TAC [][] THEN
      `∃u' v'.
         (w'' = u' ++ v) ∧ derives g1 u u' ∨
         ∃u' v'. (w'' = u ++ v') ∧ derives g2 v v'`
	    by METIS_TAC [grcDerivImpg1g2, IN_UNION] THEN
	    SRW_TAC [][] THEN
      METIS_TAC [RTC_RULES_RIGHT1]
      ]);


val concat_cfg = store_thm
("concat_cfg",
``∀g1 g2. INFINITE (UNIV:'a set)  ∧
          DISJOINT (nonTerminals g1) (nonTerminals g2)
	          ⇒
              ∃s0. (NTS (s0:'a)) ∉ (nonTerminals g1 ∪ nonTerminals g2) ∧
	            (w ∈ (conc (language g1) (language g2)) =
		     w ∈ language (grConcat s0 g1 g2))``,

SRW_TAC [][EQ_IMP_THM] THEN
 `FINITE (nonTerminals g1 ∪ nonTerminals g2)`
 by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET, FINITE_UNION] THEN
 `∃s0.s0 ∉ IMAGE stripNts (nonTerminals g1 ∪ nonTerminals g2)` by
 METIS_TAC [NOT_IN_FINITE, IMAGE_FINITE] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Q.EXISTS_TAC `s0` THEN
SRW_TAC [][]
 THENL[
       METIS_TAC [stripNts],
       METIS_TAC [stripNts],

      FULL_SIMP_TAC (srw_ss()) [conc_def] THEN
      FULL_SIMP_TAC (srw_ss()) [language_def] THEN
      `(derives (grConcat s0 g1 g2))^* [NTS (startSym g1)] u`
      by METIS_TAC [grcRtcDTog1] THEN
      `(derives (grConcat s0 g1 g2))^* [NTS (startSym g2)] v`
      by METIS_TAC [grcRtcDTog2] THEN
      `(derives (grConcat s0 g1 g2))^* [NTS (startSym g1);NTS (startSym g2)] (u++v)`
      by METIS_TAC [derives_append, APPEND] THEN
      METIS_TAC [grConcat, startSym_def, RTC_RULES, grcStartRule],


      FULL_SIMP_TAC (srw_ss()) [language_def, conc_def] THEN
      `(startSym (grConcat s0 g1 g2)) = s0`
       by METIS_TAC [grConcat, startSym_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `w ≠ [NTS s0]` by (SPOSE_NOT_THEN ASSUME_TAC THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
      METIS_TAC [grcRtcDeriv, IN_UNION, EVERY_APPEND, stripNts]
      ]);


val grClosure = Define
`grClosure s0 g =
    G (rules g++[rule s0 [NTS (startSym g); NTS s0]] ++ [rule s0 []]) s0`;

val grclRtcDTog = store_thm
("grclRtcDTog",
``∀ w w'.(derives g)^* w w' ⇒ (derives (grClosure s0 g))^* w w'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC[][] THEN
`MEM (rule lhs rhs) (rules (grClosure s0 g))` by METIS_TAC [grClosure, rules_def,
							       MEM_APPEND] THEN
METIS_TAC [res1, RTC_RULES, derives_same_append_right, derives_same_append_left]);


val grclRtcDSsym = store_thm
("grclRtcDSsym",
``(derives (grClosure s0 g))^* [NTS s0] [NTS (startSym g)]``,

SRW_TAC [][Once RTC_CASES1] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `[NTS (startSym g); NTS s0]` THEN
SRW_TAC [][derives_def, lreseq, grClosure, rules_def] THEN
SRW_TAC [][Once RTC_CASES1] THEN
Q.EXISTS_TAC `[NTS (startSym g)]` THEN
SRW_TAC [][derives_def, lreseq, grClosure, rules_def] THEN
METIS_TAC [APPEND_NIL, APPEND]);


val grclDerivNil = store_thm
("grclDerivNil",
``derives (grClosure s0 g) [NTS s0] []``,

SRW_TAC [][derives_def, grClosure, rules_def]);


val grclDerivesAppend = store_thm
("grclDerivesAppend",
``(derives g)^* [NTS (startSym g)] s1 ∧ (derives g)^* [NTS (startSym g)] s2
      ⇒
   (derives (grClosure s0 g))^* [NTS s0] (s1++s2)``,

SRW_TAC [][] THEN
`(derives (grClosure s0 g))^* [NTS (startSym g)] s1`
by METIS_TAC [grclRtcDTog, startSym_def, grClosure, grclRtcDSsym, RTC_RTC] THEN
`(derives (grClosure s0 g))^* [NTS (startSym g)] s2`
by METIS_TAC [grclRtcDTog, startSym_def, grClosure, grclRtcDSsym, RTC_RTC] THEN
`(derives (grClosure s0 g))^* [NTS (startSym g);NTS(startSym g)] (s1++s2)`
by METIS_TAC [derives_append, APPEND] THEN
`derives (grClosure s0 g) [NTS s0] [NTS (startSym g); NTS s0]`
by (SRW_TAC [][derives_def, grClosure, rules_def] THEN
    METIS_TAC [APPEND_NIL, symbol_11]) THEN
`derives (grClosure s0 g) [NTS (startSym g); NTS s0]
   [NTS (startSym g); NTS (startSym g);NTS s0]`
by (SRW_TAC [][derives_def, grClosure, rules_def] THEN
    METIS_TAC [APPEND_NIL, APPEND, symbol_11]) THEN
`derives (grClosure s0 g) [NTS (startSym g); NTS (startSym g);NTS s0]
   [NTS (startSym g); NTS (startSym g)]`
by (SRW_TAC [][derives_def, grClosure, rules_def] THEN
    METIS_TAC [APPEND_NIL, APPEND, symbol_11]) THEN
METIS_TAC [RTC_RTC, RTC_RULES]);

val grclDerivesAppend' = store_thm
("grclDerivesAppend'",
``(derives  (grClosure s0 g))^* [NTS (startSym g)] s1 ∧
 (derives (grClosure s0 g))^* [NTS s0] s2
      ⇒
   (derives (grClosure s0 g))^* [NTS s0] (s1++s2)``,

SRW_TAC [][] THEN
`(derives (grClosure s0 g))^* [NTS (startSym g);NTS s0] (s1++s2)`
by METIS_TAC [derives_append, APPEND] THEN
`derives (grClosure s0 g) [NTS s0] [NTS (startSym g);NTS s0]`
by (SRW_TAC [][derives_def, grClosure, rules_def] THEN
    METIS_TAC [APPEND_NIL, APPEND, symbol_11]) THEN
METIS_TAC [RTC_RTC, RTC_RULES]);


val grclRtcImpD =
store_thm
("grclRtcImpD",
``∀w w'.(derives (grClosure s0 g))^* w w' ⇒ (w=[NTS (startSym g)]) ⇒
         (NTS s0 ∉ nonTerminals g)
	   ⇒
	   (derives g)^* w w'``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [grClosure, rules_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [res1, derives_same_append_left, derives_same_append_right,
	   RTC_RULES_RIGHT1] THEN
(Cases_on `[NTS (startSym g)] ≠ (s1 ++ [NTS lhs] ++ s2)` THEN
 SRW_TAC [][] THEN1
 METIS_TAC [slemma1_4, rtcDerivesInRuleRhs'] THEN
 FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
 METIS_TAC [slemma1_4]));



val starImpgrcl = store_thm
("starImpgrcl",
``∀w. star (language g) w ⇒ w ∈ language (grClosure s0 g)``,

HO_MATCH_MP_TAC star_ind THEN
SRW_TAC [][language_def, EXTENSION] THEN
 `startSym (grClosure s0 g) = s0` by METIS_TAC [grClosure, startSym_def] THEN1
METIS_TAC [grclDerivNil, RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN1
METIS_TAC [grclRtcDSsym, grclRtcDTog, RTC_RTC] THEN1
METIS_TAC [grclDerivesAppend',grclRtcDSsym, grclRtcDTog,RTC_RTC]);


val grcls0Deriv = store_thm
("grcls0Deriv",
``(NTS s0 ∉ nonTerminals g) ⇒ derives (grClosure s0 g) [NTS s0] h
     ⇒
  (h=[]) ∨ (h=[NTS (startSym g);NTS s0])``,

SRW_TAC [][derives_def, lreseq, grClosure, rules_def] THEN
METIS_TAC [slemma1_4]);



val grcls0ld = store_thm
("grcls0ld",
``derives (grClosure s0 g) ⊢ h::h'::t' ◁ [NTS s0] → w ∧
   (NTS s0 ∉ nonTerminals g)
    ⇒
 (h'=[]) ∨
derives (grClosure s0 g) ⊢ h'::t' ◁ ([NTS (startSym g)]++[NTS s0]) → w``,

SRW_TAC [][listderiv_def] THEN
METIS_TAC [grcls0Deriv]);


val grclImpStarLd = store_thm
("grclImpStarLd",
``∀w'.(derives (grClosure s0 g)) ⊢ dl ◁  [NTS s0] → w' ⇒ EVERY isTmnlSym w' ⇒
 (NTS s0 ∉ nonTerminals g)
     ⇒
     star (language g) w'``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
`(h'=[]) ∨
derives (grClosure s0 g) ⊢ h'::t' ◁ ([NTS (startSym g)]++[NTS s0]) → w'`
by METIS_TAC [grcls0ld] THEN1
(SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`t'=[]` by (SPOSE_NOT_THEN ASSUME_TAC THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [rtc2list_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def]) THEN
SRW_TAC [][star_rules]) THEN
`∃x' y' dl1 dl2.
              (w' = x' ++ y') ∧
              derives (grClosure s0 g) ⊢ dl1 ◁
                 [NTS (startSym g)] → x' ∧
              derives (grClosure s0 g) ⊢ dl2 ◁
                 [NTS s0] → y' ∧
              LENGTH dl1 ≤ LENGTH (h'::t') ∧
              LENGTH dl2 ≤ LENGTH (h'::t')` by METIS_TAC [upgr_r17_ld] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH dl2`] MP_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH dl2 < SUC (SUC (LENGTH t'))` by FULL_SIMP_TAC (arith_ss) [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`dl2`] MP_TAC) THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`y'`] MP_TAC) THEN
SRW_TAC [][] THEN
SRW_TAC [][Once star_cases] THEN
DISJ2_TAC THEN
DISJ2_TAC THEN
MAP_EVERY Q.EXISTS_TAC [`x'`, `y'`] THEN
SRW_TAC [][language_def, EXTENSION] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl1=[]` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [rtc2listRtcHdLast, HD, NOT_CONS_NIL, grclRtcImpD]);

val closure_cfg = store_thm
("closure_cfg",
``∀g. INFINITE (UNIV:'a set)
           ⇒
	   ∃s0.(NTS s0) ∉ nonTerminals (g:('a,'b) grammar) ∧
      	       (star (language g) w) = w ∈ language (grClosure s0 g)``,

SRW_TAC [][EQ_IMP_THM] THEN
 `FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
 `∃s0.s0 ∉ IMAGE stripNts (nonTerminals g)` by METIS_TAC [NOT_IN_FINITE,
							  IMAGE_FINITE] THEN
 `startSym (grClosure s0 g) = s0` by METIS_TAC [grClosure, startSym_def] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Q.EXISTS_TAC `s0` THEN
SRW_TAC [][]
THENL[
      METIS_TAC [starImpgrcl],

      METIS_TAC [symbol_11, stripNts],

      `(derives (grClosure s0 g))^* [NTS (startSym (grClosure s0 g))] w ∧
      EVERY isTmnlSym w`
      by FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN
      METIS_TAC [rtc2list_exists', grclImpStarLd, stripNts, symbol_11,
		 grClosure, startSym_def, listderiv_def]
      ]);


val _ = export_theory();





