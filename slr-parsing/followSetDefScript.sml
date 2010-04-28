open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory

open symbolDefTheory grammarDefTheory listLemmasTheory firstSetDefTheory
    relationLemmasTheory

val _ = new_theory "followSetDef"

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w)

val _ = set_trace "Unicode" 1;

val _ = Globals.linewidth := 60
val _ = diminish_srw_ss ["list EQ"];

val followSet = Define 
`followSet g sym = 
{ TS ts | ∃s.MEM s (MAP ruleRhs (rules g)) ∧ 
          ∃pfx sfx.RTC (derives g) s (pfx++[sym]++[TS ts]++sfx) }`

val followRuleML_defn = Hol_defn "followRuleML_defn"
`(followRuleML g sn sym (rule l []) = {}) ∧
(followRuleML g sn sym (rule l (h::t)) = 
if (~(MEM sym sn) ∧ sym ∈ (allSyms g)) then
    if ((NTS l) IN (nonTerminalsML g)) then
	if (h=sym) then
	      set (firstSet1 g [] t) ∪ 
              followRuleML g sn sym (rule l t) ∪
	     (if nullableML g [] t then 
		BIGUNION (set 
	            (MAP (followRuleML g (sym::sn) (NTS l)) 
                      (rules g))) 
              else {})
	else followRuleML g sn sym (rule l t)
    else {}
else {})`


val (followRuleML,followRuleML_ind) = 
tprove (followRuleML_defn,
WF_REL_TAC (`inv_image  (((measure (\(g,sn). CARD ((allSyms g) DIFF (set sn))))) LEX (measure (\r.LENGTH (ruleRhs r)))) (\(g,sn,sym,r).(g,sn),r)`) THEN
SRW_TAC [] [] THEN
`FINITE (allSyms g)` 
    by METIS_TAC [FINITE_LIST_TO_SET,finiteAllSyms] THEN
SRW_TAC [] [FINITE_INSERT,FINITE_LIST_TO_SET] 
THENL[

      `sym ∈ allSyms g` by METIS_TAC [symInGr] THEN
      `((allSyms g) ∩ (sym INSERT set sn)) 
         = ((sym INSERT set sn) ∩ (allSyms g))` 
	  by METIS_TAC [INTER_COMM] THEN
      ASM_REWRITE_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
      SRW_TAC [] [ADD1] THEN
      `(allSyms g) ∩ set sn = (set sn) ∩ (allSyms g)` 
	  by METIS_TAC [INTER_COMM] THEN
      ASM_REWRITE_TAC [] THEN
      DECIDE_TAC,

      `sym IN allSyms g` by METIS_TAC [symInGr] THEN
      `~(sym ∈ set sn)` by FULL_SIMP_TAC list_ss [] THEN
      `~(sym ∈ ((allSyms g) ∩ (set sn)))` 
	  by METIS_TAC [IN_INTER] THEN
      `~(allSyms g = set sn)` by METIS_TAC [] THEN
      `CARD (allSyms g) - CARD (allSyms g ∩ set sn) 
         = CARD ((allSyms g) DIFF (set sn))` 
	  by METIS_TAC [CARD_DIFF,FINITE_LIST_TO_SET,
			FINITE_INSERT] THEN
      ASM_REWRITE_TAC [] THEN
      `sym ∈ (allSyms g DIFF set sn)` 
	  by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN 
	      METIS_TAC []) THEN
      `~((allSyms g DIFF set sn)={})` 
	  by METIS_TAC [MEMBER_NOT_EMPTY] THEN
      `~(CARD (allSyms g DIFF set sn)=0)` 
	  by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
      DECIDE_TAC])


val followSetML = Define `followSetML g sym = 
BIGUNION (set (MAP (followRuleML g [] sym) (rules g)))`


val followRuleEq1 = store_thm ("followRuleEq1",
``∀g sn sym r.
     s ∈ (followRuleML g sn sym r) ⇒      
     (∀rl rh.(r = rule rl rh) ⇒ ∃rh'. (MEM (rule rl rh') (rules g)) ∧
                                     ∃pfx.(rh' = pfx ++ rh))
        ⇒
       s ∈ (followSet g sym)``,

HO_MATCH_MP_TAC followRuleML_ind THEN
SRW_TAC [] [] THEN1
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
Cases_on `~MEM sym sn ∧ sym IN allSyms g` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN

 Cases_on `NTS l ∈ nonTerminalsML g` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `h=sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
 THENL[

  FULL_SIMP_TAC (srw_ss()) [firstSetML_def] THEN
  `s IN (firstSetList g t)` 
      by METIS_TAC [firstSet1Eq1, firstSetML_def] THEN
  FULL_SIMP_TAC (srw_ss()) [firstSetList_def, followSet] THEN
  SRW_TAC [][] THEN
  `MEM (pfx++h::t) (MAP (ruleRhs) (rules g))` by (SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN 
  METIS_TAC []) THEN
  Q.EXISTS_TAC `(pfx++h::t)` THEN SRW_TAC [] [] THEN  
  `RTC (derives g) (pfx++h::t) (pfx++[h]++[TS fst]++rst)` 
      by METIS_TAC [APPEND, APPEND_ASSOC, rtc_derives_same_append_right,
		    rtc_derives_same_append_left] THEN
  METIS_TAC [APPEND, APPEND_ASSOC],

  METIS_TAC [APPEND, APPEND_ASSOC],

  Cases_on `nullableML g [] t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`a`] MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `a` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `s ∈ followSet g (NTS l)` by METIS_TAC [APPEND_NIL, APPEND,MEM] THEN
  FULL_SIMP_TAC (srw_ss()) [followSet] THEN
  SRW_TAC [][] THEN
  Q.EXISTS_TAC `s''` THEN SRW_TAC [][] THEN
  `derives g (pfx'++[NTS l]++ [TS ts]++sfx) 
 (pfx'++pfx ++ h::t++[TS ts]++sfx)` by
  METIS_TAC [derives_same_append_left, derives_same_append_right,APPEND_ASSOC,
  res1, APPEND] THEN
  `(derives g)^* t []` by METIS_TAC [nullableML, nullableEq, nullable_def] THEN
  `(derives g)^* (pfx' ++ pfx ++ h::t ++ [TS ts] ++ sfx) 
 (pfx' ++ pfx ++ [h] ++ [TS ts] ++ sfx)` 
  by  METIS_TAC [APPEND, APPEND_ASSOC, rtc_derives_same_append_left,
  rtc_derives_same_append_right,APPEND_NIL] THEN
  METIS_TAC [RTC_RULES, RTC_RTC, APPEND_ASSOC],

  METIS_TAC [APPEND, APPEND_ASSOC]
  ]);


  
val followSetEq1 = store_thm ("followSetEq1",
``!g sym.s IN (followSetML g sym) ==> s IN (followSet g sym)``,
FULL_SIMP_TAC (srw_ss()) [followSetML] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
SRW_TAC [][] THEN
Cases_on `y` THEN
METIS_TAC [followRuleEq1, APPEND, APPEND_NIL]);


val followSetMem = store_thm ("followSetMem", 
``!u v.RTC (derives g) u v ==> (u=[NTS N]) ==> 
(v=(pfx++[NTS N']++[TS ts]++sfx)) ==> 
((TS ts) IN followSet g (NTS N'))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] 
THENL[

      `LENGTH [NTS N] = LENGTH (pfx ++ [NTS N'] ++ [TS ts] ++ sfx)` 
			       by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (arith_ss) [],

      FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq, followSet] THEN
      Q.EXISTS_TAC `u'` THEN
      SRW_TAC [] [] 
	      THENL[
		    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN
		    METIS_TAC [],
			  
		    METIS_TAC []]]);


``s ∈ followSet g sym ⇒ s ∈ followSetML g sym``,

SRW_TAC [][followSet] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
Cases_on `y` THEN FULL_SIMP_TAC  (srw_ss()) [] THEN
SRW_TAC [][]

``TS ts ∈ followRuleML g [] sym (rule s l)``

``∀x y. (derives g)^* x y ⇒ 
∀pfx sfx m. (x = pfx++m++sfx) ⇒ MEM m (MAP ruleRhs (rules g)) ⇒
∀p s sym ts. (y = pfx ++ p ++ [sym] ++ [TS ts] ++ s ++ sfx) ⇒
TS ts ∈ followSetML g sym``


HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
`m = p ++ [sym]++[TS ts]++s`by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
SRW_TAC [][] THEN
MAGIC


FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
`MEM rhs (MAP ruleRhs (rules g))` by MAGIC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`s2`,`rhs`] MP_TAC) THEN SRW_TAC [][] THEN


``∀pfx m sfx dl y.
derives g ⊢ dl ◁ (pfx ++ m ++ sfx) → y ⇒
∀p s sym ts.(y = pfx ++ p ++ [sym] ++ [TS ts] ++ s ++ sfx)  ⇒
(∀e. MEM e dl ⇒ ∃m'.(e= pfx ++ m' ++ sfx)) ⇒
(∀e1 e2. ∃pd sd. (dl = pd ++ [e1;e2] ++ sd) ⇒ LENGTH e2 ≥ LENGTH e1)
⇒
TS ts ∈ followSetML g sym``

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN

Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
MAGIC



IMP_RES_TAC 




val mlDir = ref ("./theoryML/");


(*
val _ =
 let open EmitML
 in emitML (!mlDir)
   ("followSet",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree", "firstSet"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: DATATYPE `item = item of string => symbol list # symbol list`
    :: DEFN firstSet1
    :: DEFN followRuleML
    :: DEFN followSetML
    :: [])
 end;
*)

val _ = export_theory ();