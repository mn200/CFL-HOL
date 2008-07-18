open HolKernel boolLib bossLib Parse BasicProvers Defn
open listTheory containerTheory pred_setTheory arithmeticTheory relationTheory markerTheory
open regexpTheory grammarDefTheory listLemmasTheory parserDefTheory 

val _ = new_theory "firstSetDef"

val firstSet = Define 
`firstSet g sym = {(TS fst) | ?rst.RTC (derives g) [sym] ([TS fst]++rst)}`

val firstSet1_defn = Hol_defn "firstSet1_defn" `
(firstSet1 g sn [] = []) /\
(firstSet1 g sn [TS ts] = [TS ts]) /\
(firstSet1 g sn [NTS nt] = if (MEM (NTS nt) sn) then [] else
				let 
				  r = getRhs nt (rules g)
				in
				   if r=[] then [] 
				   else  
				       (rmDupes ((FLAT (MAP (firstSet1 g ((NTS nt)::sn)) r))))) /\
(firstSet1 g sn (i::il) =  if isTmnlSym i then [i]
                         else if (nullableML g [] [i]) then 
			     (firstSet1 g sn [i]++firstSet1 g sn il) else  (firstSet1 g sn [i]))`


val (firstSet1,firstSet1_ind) = tprove (firstSet1_defn,
WF_REL_TAC (`inv_image ((measure (\(g,sn). CARD ((nonTerminals g) DIFF (LIST_TO_SET sn)))) LEX (measure (\(syms).LENGTH syms))) (\(g,sn,syms).((g,sn),syms))`) THEN
SRW_TAC [] [] THENL[
`FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
`FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`FINITE (NTS A INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
FULL_SIMP_TAC (srw_ss()) [CARD_DIFF] THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [CARD_INSERT,FINITE_LIST_TO_SET] THEN
`~(getRhs nt (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
`(NTS nt) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
`(nonTerminals g INTER (NTS nt INSERT set sn)) = (NTS nt INSERT set sn) INTER nonTerminals g` by METIS_TAC [INTER_COMM] THEN
ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
SRW_TAC [] [ADD1] THEN
`(nonTerminals g INTER set sn) = (set sn INTER nonTerminals g)` by METIS_TAC [INTER_COMM] THEN
ASM_REWRITE_TAC [] THEN
DECIDE_TAC,

`~(getRhs nt (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
`(NTS nt) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
`~((NTS nt) IN set sn)` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
`~(NTS nt IN (nonTerminals g INTER set sn))` by METIS_TAC [IN_INTER] THEN
`~(nonTerminals g = set sn)` by METIS_TAC [] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
`FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`FINITE (NTS nt INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
`CARD (nonTerminals g) - CARD (nonTerminals g INTER set sn) = CARD ((nonTerminals g) DIFF (set sn))` by METIS_TAC [CARD_DIFF] THEN
ASM_REWRITE_TAC [] THEN
`(NTS nt) IN (nonTerminals g DIFF set sn)` by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
`~((nonTerminals g DIFF set sn)={})` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
`~(CARD (nonTerminals g DIFF set sn)=0)` by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
DECIDE_TAC],

DECIDE_TAC,
DECIDE_TAC,
DECIDE_TAC,
DECIDE_TAC
])


val firstSetML = Define `firstSetML g sym = firstSet1 g [] [sym]`

val getRhsNilMem = store_thm ("getRhsNilMem",
``(getRhs nt (rules g) =[]) = ~(?r.MEM (rule nt r) (rules g))``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
Induct_on `l` THEN
SRW_TAC [] [getRhs_def] THEN
SRW_TAC [] [] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs_def] THEN
Cases_on `nt=s` THEN
SRW_TAC [] [] THEN
METIS_TAC [getRhsDistrib,APPEND,APPEND_eq_NIL])

val getRhsNilRtc = store_thm ("getRhsNilRtc", 
``(getRhs nt (rules g) = []) ==> (!l.RTC (derives g) [NTS nt] l ==> (l=[NTS nt]))``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq,getRhsNilMem] THEN
METIS_TAC [])

(*
NOT BEING USED
val diff_r1 = mk_thm ([], ``!x y.MEM e y ==> (diff x y = diff x (e::y))``)


val diff_r2 = mk_thm ([], ``!x y.~(MEM e y) ==> (diff x y = e::(diff x (e::y)))``)

val diff_r3 = mk_thm ([], ``!x y.~MEM h (diff x (h::y))``)

*)

val rmd_r0 = mk_thm ([], ``!x y.rmDupes (x++y) = (rmDupes x ++ rmDupes (diff y x))``)

val rmd_r1 = store_thm ("rmd_r1", 
``!x y z.rmDupes (x++y++z) = (rmDupes x ++ rmDupes (diff y x) ++ rmDupes (diff z (x++y)))``,
SRW_TAC [] [] THEN
METIS_TAC [APPEND_ASSOC,rmd_r0])

val derivesFirstSet = store_thm ("derivesFirstSet",
``derives g [NTS nt] (TS ts::sfx) ==> MEM (TS ts) (firstSet1 g [] [NTS nt])``,
SRW_TAC [] [] THEN
`MEM (TS ts::sfx) (getRhs nt (rules g))` by METIS_TAC [x_1] THEN
FULL_SIMP_TAC (srw_ss()) [firstSet1,rgr_r9eq] THEN
SRW_TAC [] [Abbrev_def,LET_THM] THEN
Induct_on `sfx` THEN
SRW_TAC [] [firstSet1] THEN

SRW_TAC [] [rmd_r1] THEN
`MEM (TS ts) ((FLAT (MAP (\a.firstSet1 g [NTS nt] a) r1)) ++ [TS ts] ++ (FLAT (MAP (\a.firstSet1 g [NTS nt] a) r2)))` by SRW_TAC [] [] THEN
SRW_TAC [] [FLAT_APPEND_DISTRIB,FILTER_APPEND_DISTRIB] THENL[
METIS_TAC [rgr_r9eq,rmd_r1,rmd_r2],
METIS_TAC [rgr_r9eq,rmd_r1,rmd_r2],
METIS_TAC [isTmnlSym_def],
METIS_TAC [isTmnlSym_def]])

val firstSetList = Define `firstSetList g l = {TS fst | ?rst. RTC (derives g) l ([TS fst] ++ rst)}`

val firstSet1Eq1 = store_thm ("firstSet1Eq1",
``!g sn l.((MEM s (firstSet1 g sn l)) ==> (s IN (firstSetList g l)))``,
HO_MATCH_MP_TAC firstSet1_ind THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList] THEN METIS_TAC [b1],

FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList] THEN METIS_TAC [RTC_RULES],

FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList, LET_THM] THEN
Cases_on `MEM (NTS nt) sn` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `getRhs nt (rules g) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM s ((FLAT (MAP (\a. firstSet1 g (NTS nt::sn) a) (getRhs nt (rules g)))))` by METIS_TAC [rmd_r2] THEN
`?e. MEM e (MAP (\a.firstSet1 g (NTS nt::sn) a) (getRhs nt (rules g))) /\ (MEM s e)` by METIS_TAC [flat_map_mem] THEN
`?l.(MEM l (getRhs nt (rules g))) /\ (MEM s (firstSet1 g (NTS nt::sn) l))` by METIS_TAC [MEM_MAP] THEN
RES_TAC THEN
Q.EXISTS_TAC `fst` THEN
SRW_TAC [] [] THEN
METIS_TAC [x_1, RTC_RULES],


FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList, LET_THM, isTmnlSym_def] THEN
Cases_on `MEM (NTS v7) sn` THEN Cases_on `(getRhs v7 (rules g)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `nullableML g [] [NTS v7]` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`nullable g [NTS v7]` by METIS_TAC [nullableEq] THEN
FULL_SIMP_TAC (srw_ss()) [nullable_def] THEN
METIS_TAC [derives_append, APPEND], 

`nullable g [NTS v7]` by METIS_TAC [nullableEq] THEN
FULL_SIMP_TAC (srw_ss()) [nullable_def] THEN
METIS_TAC [derives_append, APPEND],

`nullable g [NTS v7]` by METIS_TAC [nullableEq] THEN
FULL_SIMP_TAC (srw_ss()) [nullable_def] THEN
METIS_TAC [derives_append, APPEND],

FULL_SIMP_TAC (srw_ss()) [] THEN
`?rst1.RTC (derives g) [v14] rst1` by METIS_TAC [RTC_RULES] THEN
`?rst2.RTC (derives g) v15 rst2` by METIS_TAC [RTC_RULES] THEN
`RTC (derives g) ([v14]++v15) (rst1++rst2)` by FULL_SIMP_TAC (srw_ss()) [derives_append, APPEND, CONS, APPEND_ASSOC]  THEN
`RTC (derives g) ([NTS v7] ++ [v14] ++ v15) ((TS fst::rst)++rst1++rst2)` by FULL_SIMP_TAC (srw_ss()) [derives_append, APPEND, CONS, APPEND_ASSOC]  THEN
METIS_TAC [APPEND,APPEND_ASSOC],

RES_TAC THEN
`nullable g [NTS v7]` by METIS_TAC [nullableEq] THEN
FULL_SIMP_TAC (srw_ss()) [nullable_def] THEN
`RTC (derives g) ([NTS v7] ++ (v14::v15))([] ++ (TS fst::rst))` by FULL_SIMP_TAC (srw_ss()) [derives_append, APPEND, CONS, APPEND_ASSOC] THEN
METIS_TAC [APPEND,APPEND_ASSOC, CONS, derives_append, nullableEq, nullable_def],

FULL_SIMP_TAC (srw_ss()) [] THEN
`?rst1.RTC (derives g) [v14] rst1` by METIS_TAC [RTC_RULES] THEN
`?rst2.RTC (derives g) v15 rst2` by METIS_TAC [RTC_RULES] THEN
`RTC (derives g) ([v14]++v15) (rst1++rst2)` by FULL_SIMP_TAC (srw_ss()) [derives_append, APPEND, CONS, APPEND_ASSOC]  THEN
`RTC (derives g) ([NTS v7] ++ [v14] ++ v15) ((TS fst::rst)++rst1++rst2)` by FULL_SIMP_TAC (srw_ss()) [derives_append, APPEND, CONS, APPEND_ASSOC]  THEN
METIS_TAC [APPEND,APPEND_ASSOC]],


FULL_SIMP_TAC (srw_ss()) [firstSetList, firstSet1, isTmnlSym_def] THEN
`RTC (derives g) [TS v6] [TS v6]` by METIS_TAC [RTC_RULES] THEN
`?rst1.RTC (derives g) [v10] rst1` by METIS_TAC [RTC_RULES] THEN
`?rst2.RTC (derives g) v11 rst2` by METIS_TAC [RTC_RULES] THEN
`RTC (derives g) ([TS v6] ++ [v10] ++ v11) ([TS v6]++rst1++rst2)` by FULL_SIMP_TAC (srw_ss()) [derives_append, APPEND, CONS, APPEND_ASSOC]  THEN
METIS_TAC [APPEND,APPEND_ASSOC]]
)


(*
``!g sn l.(s IN (firstSetList g l)) ==> (sn=[]) ==> (MEM s (firstSet1 g sn l))``
HO_MATCH_MP_TAC firstSet1_ind THEN SRW_TAC [] [] THENL[

FULL_SIMP_TAC (srw_ss()) [firstSetList, firstSet1, Once RTC_CASES1, derives_def],


FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList, notTmnlRtcDerives],

FULL_SIMP_TAC (srw_ss()) [firstSetList, firstSet1]
Cases_on `MEM (NTS nt sn)`



 
*)






val _ = save_thm ("firstSet1",firstSet1)
val _ = save_thm ("firstSet1_ind",firstSet1_ind)

val firstSet1Eq = mk_thm ([],
``!g sn l.((MEM s (firstSet1 g sn l)) = (s IN (firstSetList g l)))``)


val _ = save_thm ("firstSet1",firstSet1)
val _ = save_thm ("firstSet1_ind",firstSet1_ind)


val mlDir = ref ("./theoryML/");

val _ =
 let open EmitML
 in emitML (!mlDir)
   ("firstSet",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: DATATYPE `item = item of string => symbol list # symbol list`
    :: DEFN firstSet1
    :: DEFN firstSetML
    :: [])
 end;



val _ = export_theory ();

