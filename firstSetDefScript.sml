open HolKernel boolLib bossLib Parse BasicProvers Defn
open listTheory containerTheory pred_setTheory arithmeticTheory relationTheory markerTheory
open regexpTheory grammarDefTheory listLemmasTheory

val _ = new_theory "firstSetDef"

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w)


val _ = Globals.linewidth := 60

val firstSet = Define
`firstSet g sym =
{(TS fst) | ?rst.RTC (derives g) [sym] ([TS fst]++rst)}`

val _ = set_trace "Unicode" 1;

val firstSet1_defn = Hol_defn "firstSet1_defn" `
  (firstSet1 g sn [] = []) ∧
  (firstSet1 g sn (TS ts :: rest) = [TS ts]) ∧
  (firstSet1 g sn (NTS nt :: rest) =
     if MEM (NTS nt) sn then [] else
     let
       r = getRhs nt (rules g)
     in
       rmDupes ((FLAT (MAP (firstSet1 g (NTS nt::sn)) r))))`


val (firstSet1,firstSet1_ind) = tprove (
  firstSet1_defn,
  WF_REL_TAC
   `inv_image (measure (λ(g,sn). CARD (nonTerminals g DIFF LIST_TO_SET sn))
                 LEX
               measure (λ(syms).LENGTH syms))
              (λ(g,sn,syms).((g,sn),syms))` THEN
  SRW_TAC [] [] THEN
  `FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
  `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
  `FINITE (NTS A INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
  SRW_TAC [] [CARD_DIFF] THENL[
    SRW_TAC [] [CARD_INSERT,FINITE_LIST_TO_SET] THEN
    `~(getRhs nt (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `(NTS nt) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `(nonTerminals g ∩ (NTS nt INSERT set sn)) =
       (NTS nt INSERT set sn) ∩ nonTerminals g` by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
    SRW_TAC [] [ADD1] THEN
    `(nonTerminals g ∩ set sn) = (set sn ∩ nonTerminals g)`
       by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    DECIDE_TAC,

    `~(getRhs nt (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `(NTS nt) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `~((NTS nt) IN set sn)` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
    `~(NTS nt IN (nonTerminals g INTER set sn))` by METIS_TAC [IN_INTER] THEN
    `~(nonTerminals g = set sn)` by METIS_TAC [] THEN
    `FINITE (nonTerminals g)`
       by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
    `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
    `FINITE (NTS nt INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
    `CARD (nonTerminals g) - CARD (nonTerminals g ∩ set sn) =
       CARD (nonTerminals g DIFF set sn)`
       by METIS_TAC [CARD_DIFF] THEN
    ASM_REWRITE_TAC [] THEN
    `NTS nt ∈ (nonTerminals g DIFF set sn)` by
       (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
    `~((nonTerminals g DIFF set sn)={})` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
    `~(CARD (nonTerminals g DIFF set sn)=0)`
       by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
    DECIDE_TAC
  ]);

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
``(getRhs nt (rules g) = []) ==>
      (!l.RTC (derives g) [NTS nt] l ==> (l=[NTS nt]))``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq,getRhsNilMem] THEN
METIS_TAC [])

(*
NOT BEING USED
val diff_r1 = mk_thm ([], ``!x y.MEM e y ==> (diff x y = diff x (e::y))``)


val diff_r2 = mk_thm ([], ``!x y.~(MEM e y) ==> (diff x y = e::(diff x (e::y)))``)

val diff_r3 = mk_thm ([], ``!x y.~MEM h (diff x (h::y))``)


val rmd_r0 = store_thm ("rmd_r0",
``!x y.rmDupes (x++y) = (rmDupes x ++ rmDupes (diff y x))``,
HO_MATCH_MP_TAC diff_ind THEN
SRW_TAC [][diff_def,rmDupes] THEN
FULL_SIMP_TAC (srw_ss()) [delete_def,delete_append,rmd_del] THEN
MAGIC)



val rmd_r1 = store_thm ("rmd_r1",
``!x y z.rmDupes (x++y++z) = (
rmDupes x ++ rmDupes (diff y x) ++ rmDupes (diff z (x++y)))``,
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

*)

val MEM_getRhs = store_thm(
  "MEM_getRhs",
  ``MEM r (getRhs N l) = MEM (rule N r) l``,
  Induct_on `l` THEN SRW_TAC [][getRhs_def] THEN
  Cases_on `h` THEN SRW_TAC [][getRhs_def] THEN SRW_TAC [][]);


val firstSetList = Define
`firstSetList g l =
      {TS fst | ?rst. RTC (derives g) l ([TS fst] ++ rst)}`

val firstSet1Eq1 = store_thm ("firstSet1Eq1",
  ``∀g sn l. MEM s (firstSet1 g sn l) ==> s ∈ firstSetList g l``,
  HO_MATCH_MP_TAC firstSet1_ind THEN SRW_TAC [] [firstSet1] THENL[
    SIMP_TAC (srw_ss()) [firstSetList] THEN METIS_TAC [RTC_RULES],

    FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList, LET_THM,
                              rmd_mem_list] THEN
    `∃e. MEM e (MAP (\a.firstSet1 g (NTS nt::sn) a)
               (getRhs nt (rules g))) /\ (MEM s e)`
        by METIS_TAC [flat_map_mem] THEN
    `∃l. MEM l (getRhs nt (rules g)) ∧ MEM s (firstSet1 g (NTS nt::sn) l)`
       by METIS_TAC [MEM_MAP] THEN
    RES_TAC THEN
    `MEM (rule nt l) (rules g)` by METIS_TAC [MEM_getRhs] THEN
    Q.EXISTS_TAC `fst` THEN SRW_TAC [][] THEN
    `derives g (NTS nt :: rest) (l ++ rest)`
        by METIS_TAC [derives_same_append_right, APPEND, res1] THEN
    Q.EXISTS_TAC `rst ++ rest` THEN
    `(derives g)^* (l ++ rest) ((TS fst :: rst) ++ rest)`
       by METIS_TAC [rtc_derives_same_append_right] THEN
    METIS_TAC [RTC_RULES, APPEND, APPEND_ASSOC]
  ]);

open rich_listTheory

val rtc2list_fs_split = store_thm
("rtc2list_fs_split",
``!dl.rtc2list (derives g) dl ==>
!s.MEM (TS s) (LAST dl) ==>
!N.MEM (NTS N) (HD dl) ==>
 RTC (derives g) [NTS N] (TS s::rst) ==>
 (?pfx sfx.(HD dl =pfx++[NTS N]++sfx) /\
             ~(TS s IN firstSetList g pfx)) ==>
  ?pfx' sfx'.(LAST dl = (pfx'++TS s::rst++sfx')) /\
           ?dl'.rtc2list (derives g) dl' /\
                (HD dl' =  [NTS N]) /\
                (LAST dl' = TS s::rhs) /\
                (LENGTH dl' <= LENGTH dl)``,
MAGIC)


val rtc2list_isolate_FsNT = store_thm(
  "rtc2list_isolate_FsNT",
  ``!dl.rtc2list (derives g) dl ==>
    !pfx N sfx.
               (HD dl =  (pfx++[NTS N]++sfx)) ==>
	       !pfx' t rst sfx'.
                RTC (derives g) pfx pfx' ==>
		RTC (derives g) sfx sfx' ==>
                RTC (derives g) [NTS N] (TS t::rst) ==>
                (LAST dl = pfx'++TS t::rst++sfx') ==>
                   ?dl'.rtc2list (derives g) dl'
                      /\ (HD dl' = [NTS N]) /\
                        (LAST  dl' = TS t::rst) /\
                        (LENGTH dl' <= LENGTH dl)``,
  HO_MATCH_MP_TAC SNOC_INDUCT THEN
  SRW_TAC [][SNOC_APPEND, last_append] THEN
  Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][]  THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
MAP_EVERY Q.EXISTS_TAC [`r1`] THEN

Cases_on `LENGTH dl = 1`
THENL[
      Cases_on `dl` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      Q.EXISTS_TAC `[[NTS N];TS t::rst]` THEN
      SRW_TAC [][] THEN



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
  `(?pfx2. derives g pfx' pfx2 /\ (x = pfx2 ++ rhs ++ sfx')) \/
   (?rhs2. derives g rhs rhs2 /\ (x = pfx' ++ rhs2 ++ sfx')) \/
   (?sfx2. derives g sfx' sfx2 /\ (x = pfx' ++ rhs ++ sfx2))`
     by (Q.PAT_ASSUM `LAST dl = X` SUBST_ALL_TAC THEN
         FULL_SIMP_TAC (srw_ss()) [lemma2']) THEN
  SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`pfx2`, `LAST dl'`, `sfx'`] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `dl'` THEN SRW_TAC [ARITH_ss][],

    MAP_EVERY Q.EXISTS_TAC [`pfx'`, `rhs2`, `sfx'`] THEN
    SRW_TAC[][] THEN
    Q.EXISTS_TAC `dl' ++ [rhs2]` THEN
    SRW_TAC [][rtc2list_append_right] THENL[
      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [],
      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [last_append]
    ],

    MAP_EVERY Q.EXISTS_TAC [`pfx'`, `LAST dl'`, `sfx2`] THEN
    SRW_TAC [][] THEN Q.EXISTS_TAC `dl'` THEN
    SRW_TAC [ARITH_ss][]
  ]])



val rtc2listFsExists =
store_thm ("rtc2listFsExists",
``!dl.rtc2list (derives g) dl ==>
  (HD dl = [NTS N]) ==>
  (LAST dl = TS ts::sfx) ==>
   ~(TL dl = []) ==>
   ?sfx'.(HD (TL dl) = TS ts::sfx') \/
   ?pfx' N' sfx'.(HD (TL dl) = pfx'++[NTS N']++sfx')
		/\ nullable g pfx'
                /\ (TS ts IN firstSet g (NTS N'))
                /\ ~(TS ts IN firstSetList g pfx')``,

SRW_TAC [][] THEN
`~(dl=[])` by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
`RTC (derives g) [NTS N] (TS ts::sfx)`
by METIS_TAC [rtc2listRtcHdLast] THEN
Cases_on `TL dl` THEN SRW_TAC [][] THEN
`dl=[HD dl]++TL dl` by METIS_TAC [listHdTl] THEN
`rtc2list (derives g) (TL dl) `
by METIS_TAC [rtc2list_distrib_append_snd,NOT_CONS_NIL] THEN
`LAST dl = LAST (TL dl)`
by METIS_TAC [last_append,NOT_CONS_NIL] THEN
`RTC (derives g) h (TS ts::sfx)`
by METIS_TAC [rtc2listRtcHdLast,HD,NOT_CONS_NIL] THEN
`derives g [NTS N] h`
by METIS_TAC [rtc2list_def,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
MAGIC)


val rtc_fs_split = store_thm
("rtc_fs_split",
``!u v.RTC (derives g) u v ==>
  (u=pfx++[NTS N]++sfx) ==>
  MEM (TS s) v ==>
  (TS s IN firstSet g (NTS N)) ==>
  ~(TS s IN firstSetList g pfx) ==>
  ?pfx' rhs sfx'.(v = (pfx'++TS s::rhs++rst)) /\
           RTC (derives g) pfx pfx' /\
           RTC (derives g) [NTS N] (TS s::rhs) /\
           RTC (derives g) sfx sfx'``,
MAGIC)


(*
``!g sn l.(s IN (firstSetList g l)) ==>
  (sn=[]) ==> (MEM s (firstSet1 g sn l))``
HO_MATCH_MP_TAC firstSet1_ind THEN SRW_TAC [] []
THENL[

FULL_SIMP_TAC (srw_ss()) [firstSetList, firstSet1, Once RTC_CASES1, derives_def],

FULL_SIMP_TAC (srw_ss()) [firstSetList, firstSet1, Once RTC_CASES1, derives_def,lreseq],


FULL_SIMP_TAC (srw_ss()) [firstSetList, firstSet1,LET_THM]
Cases_on `MEM (NTS nt sn)`


``rtc2list (derives g) dl ==>
  ~(dl=[]) ==>
   !N sfx.(HD dl = [NTS N]) ==>
      (LAST dl = TS ts::sfx) ==>
   MEM (TS ts) (firstSetML g sn (NTS N))``
completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `TL dl=[]` THEN
SRW_TAC [][]
THENL[
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [],

      IMP_RES_TAC rtc2listFsExists
      THENL[
	    `dl = [HD dl]++TL dl`by METIS_TAC [listHdTl] THEN
	    `derives g [NTS N] (TS ts::sfx')`
		by METIS_TAC [rtc2list_def,APPEND,listHdTl] THEN
	    FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
	    `?r1 r2.rules g = r1++[rule N (TS ts::sfx')]++r2`
		by METIS_TAC [rgr_r9eq] THEN
	    FULL_SIMP_TAC (srw_ss()) [getRhsDistrib,getRhs_def] THEN
	    SRW_TAC [] [firstSetML,firstSet1,LET_THM]  THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    THENL[
		  FULL_SIMP_TAC (srw_ss()) [getRhsDistrib,getRhs_def],

		  Cases_on `sfx'` THEN
		  SRW_TAC [][firstSet1,FLAT_APPEND_DISTRIB] THEN
		  FULL_SIMP_TAC (srw_ss()) [getRhsDistrib,getRhs_def] THEN
		  SRW_TAC [] [firstSet1,FLAT_APPEND_DISTRIB] THEN
		  METIS_TAC [MEM,MEM_APPEND,rmd_mem_list]
		  ],

	    `dl = [HD dl]++TL dl`by METIS_TAC [listHdTl] THEN
	    `LENGTH (TL dl) < LENGTH ([HD dl]++TL dl)`
		by (FULL_SIMP_TAC (srw_ss()) [] THEN
		    DECIDE_TAC) THEN
	    `rtc2list (derives g) (TL dl)`
		by METIS_TAC [rtc2list_distrib_append_snd] THEN
	    `?pfx' rhs sfx'.
             (LAST (TL dl) = pfx' ++ rhs ++ sfx') /\
             ?dl'.
               rtc2list (derives g) dl' /\ (HD dl' = [NTS N']) /\
               (LAST dl' = rhs) /\ LENGTH dl' <= LENGTH (TL dl)`
		by METIS_TAC [rtc2list_isolate_NT] THEN
	    `LENGTH (TL dl) < LENGTH dl` by METIS_TAC [] THEN
	    `LENGTH dl' < LENGTH dl`
		by (FULL_SIMP_TAC (srw_ss()) [] THEN
		    FULL_SIMP_TAC (arith_ss) []) THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH dl'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`dl'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `~(dl'=[])` by METIS_TAC [rtc2list_def] THEN
	    `LAST (TL dl) = TS ts::sfx` by METIS_TAC [last_append] THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    `(LAST dl' = TS ts::sfx)`
		by METIS_TAC [last_append] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`N'`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `LAST (TL dl) = TS ts::sfx`


      ]








*)






val _ = save_thm ("firstSet1",firstSet1)
val _ = save_thm ("firstSet1_ind",firstSet1_ind)

val firstSet1Eq = mk_thm ([],
``!g sn l.((MEM s (firstSet1 g sn l)) = (s IN (firstSetList g l)))``)


val _ = save_thm ("firstSet1",firstSet1)
val _ = save_thm ("firstSet1_ind",firstSet1_ind)


val mlDir = "./theoryML/"
(* local open parseTreeTheory in end
val _ =
 let open EmitML
 in emitML mlDir
   ("firstSet",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "set","num", "parseTree"]
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
*)


val _ = export_theory ();

