open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
     relationTheory markerTheory

open symbolDefTheory grammarDefTheory listLemmasTheory

val _ = new_theory "firstSetDef"

val _ = set_trace "Unicode" 1;

val _ = Globals.linewidth := 60
val _ = diminish_srw_ss ["list EQ"];

val firstSet =
 Define
  `firstSet g sym = {TS fst | ∃rst. RTC (derives g) [sym] ([TS fst]++rst) }`


val firstSetML = tDefine
  "firstSetML" `
  (firstSetML (g:(α,β) grammar) (sn:(α,β) symbol list) ([]:(α,β) symbol list)
       = []:(α,β) symbol list) ∧
  (firstSetML g sn (TS ts :: rest) = [TS ts]) ∧
  (firstSetML g sn (NTS nt :: rest) =
     rmDupes
     (if MEM (NTS nt) sn then []
      else let
	      r = getRhs nt (rules g)
	  in
	      FLAT (MAP (firstSetML g (NTS nt::sn)) r))
     ++ (if nullableML g [] [NTS nt] then
	    firstSetML g sn rest
	 else []))`
 (WF_REL_TAC
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

val firstSetML_ind = fetch "-" "firstSetML_ind";

val firstSetMLList = Define `firstSetMLList g sym = firstSetML g [] [sym]`;

val getRhsNilMem = store_thm ("getRhsNilMem",
``(getRhs nt (rules g) = []) = ~∃r.MEM (rule nt r) (rules g)``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
Induct_on `l` THEN
SRW_TAC [] [getRhs_def] THEN
SRW_TAC [] [] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs_def] THEN
Cases_on `nt=n` THEN
SRW_TAC [] [] THEN
METIS_TAC [getRhsDistrib,APPEND,APPEND_eq_NIL]);

val getRhsNilRtc = store_thm ("getRhsNilRtc",
``(getRhs nt (rules g) = []) ⇒
      (∀l.RTC (derives g) [NTS nt] l ⇒ (l=[NTS nt]))``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq,getRhsNilMem] THEN
METIS_TAC []);


val MEM_getRhs = store_thm(
  "MEM_getRhs",
  ``MEM r (getRhs N l) = MEM (rule N r) l``,
  Induct_on `l` THEN SRW_TAC [][getRhs_def] THEN
  Cases_on `h` THEN SRW_TAC [][getRhs_def] THEN SRW_TAC [][]);


val firstSetList =
 Define
  `firstSetList g l = {TS fst | ∃rst. RTC (derives g) l ([TS fst] ++ rst)}`

val firstSetMLEq1 = store_thm ("firstSetMLEq1",
  ``∀g sn l. MEM s (firstSetML g sn l) ⇒ s ∈ firstSetList g l``,
  HO_MATCH_MP_TAC firstSetML_ind THEN
  SRW_TAC [] [firstSetML, rmd_mem_list] THENL[
    SIMP_TAC (srw_ss()) [firstSetList] THEN METIS_TAC [RTC_RULES],

    FULL_SIMP_TAC (srw_ss()) [firstSetML, firstSetList, LET_THM,
                              rmd_mem_list] THEN
    SRW_TAC [][] THEN
    METIS_TAC [nullableEq,nullable_def,APPEND_NIL,
	       derives_append,APPEND],


    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    `∃e. MEM e (MAP (\a.firstSetML g (NTS nt::sn) a)
               (getRhs nt (rules g))) /\ (MEM s e)`
        by METIS_TAC [flat_map_mem] THEN
    `∃l. MEM l (getRhs nt (rules g)) ∧
          MEM s (firstSetML g (NTS nt::sn) l)`
       by METIS_TAC [MEM_MAP] THEN
    RES_TAC THEN
    SRW_TAC [][] THEN
    `MEM (rule nt l') (rules g)` by METIS_TAC [MEM_getRhs] THEN
    SRW_TAC [] [firstSetList] THEN
    `derives g (NTS nt :: l) (l' ++ l)`
        by METIS_TAC [derives_same_append_right, APPEND, res1] THEN
    FULL_SIMP_TAC (srw_ss()) [firstSetList] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `rst ++ l` THEN
    `(derives g)^* (l' ++ l) ((TS fst :: rst) ++ l)`
       by METIS_TAC [rtc_derives_same_append_right] THEN
    METIS_TAC [RTC_RULES, APPEND, APPEND_ASSOC],

    FULL_SIMP_TAC (srw_ss()) [firstSetList] THEN
    SRW_TAC [][] THEN
    METIS_TAC [nullableEq,nullable_def,APPEND_NIL,
	       derives_append,APPEND],

    FULL_SIMP_TAC (srw_ss()) [LET_THM,firstSetList] THEN
    `∃e. MEM e (MAP (\a.firstSetML g (NTS nt::sn) a)
               (getRhs nt (rules g))) /\ (MEM s e)`
        by METIS_TAC [flat_map_mem] THEN
    `∃l. MEM l (getRhs nt (rules g)) ∧
       MEM s (firstSetML g (NTS nt::sn) l)`
       by METIS_TAC [MEM_MAP] THEN
    RES_TAC THEN
    SRW_TAC [][] THEN
    `MEM (rule nt l') (rules g)` by METIS_TAC [MEM_getRhs] THEN
    SRW_TAC [] [firstSetList] THEN
    `derives g (NTS nt :: l) (l' ++ l)`
        by METIS_TAC [derives_same_append_right, APPEND, res1] THEN
    FULL_SIMP_TAC (srw_ss()) [firstSetList] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `rst ++ l` THEN
    `(derives g)^* (l' ++ l) ((TS fst :: rst) ++ l)`
       by METIS_TAC [rtc_derives_same_append_right] THEN
    METIS_TAC [RTC_RULES, APPEND, APPEND_ASSOC]
    ]);

open rich_listTheory;


val ntderive_def = Define`
  (ntderive g tok [] = F) ∧
  (ntderive g tok [N] =
     ∃pfx sfx rhs.
        MEM (rule N rhs) (rules g) ∧
        (rhs = pfx ++ [TS tok] ++ sfx) ∧
        nullable g pfx) ∧
  (ntderive g tok (N1 :: N2 :: Ns) =
     ∃pfx sfx rhs.
        MEM (rule N1 rhs) (rules g) ∧
        (rhs = pfx ++ [NTS N2] ++ sfx) ∧
        nullable g pfx ∧
        ntderive g tok (N2 :: Ns))
`;
val _ = export_rewrites ["ntderive_def"];

val ntderive_APPEND = store_thm(
  "ntderive_APPEND",
  ``∀l1 l2. ntderive g tok (l1 ++ l2) ∧ ¬(l2 = []) ⇒
            ntderive g tok l2``,
  Induct THEN1 SRW_TAC [][] THEN
  Cases_on `l1` THEN SRW_TAC [][] THENL [
    Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [APPEND]
  ]);

val MEM_FLAT = prove(
  ``MEM e (FLAT l) = ∃l0. MEM l0 l ∧ MEM e l0``,
  Induct_on `l` THEN SRW_TAC [][] THEN METIS_TAC []);

val nullable_TS = prove(
  ``nullable g (TS s :: rest) = F``,
  SRW_TAC [][nullable_def] THEN
  METIS_TAC [notTlRtcDerives]);

val firstset1_nullable_append = store_thm("firstset1_nullable_append",
  ``MEM t (firstSetML g sn sfx) ∧ nullable g pfx ⇒
    MEM t (firstSetML g sn (pfx ++ sfx))``,
  Induct_on `pfx` THEN SRW_TAC [][] THEN
  `nullable g [h] ∧ nullable g pfx`
     by METIS_TAC [nullable_APPEND, APPEND] THEN
  `∃N. h = NTS N`
     by (Cases_on `h` THEN
	 FULL_SIMP_TAC (srw_ss()) [nullable_TS]) THEN
  SRW_TAC [][firstSetML, rmd_mem_list, GSYM nullableEq]);

val firstset1_cons_I = store_thm("firstset1_cons_I",
  ``MEM tok (firstSetML g sn [h]) ⇒
    MEM tok (firstSetML g sn (h :: t))``,
  Cases_on `h` THEN SRW_TAC [][firstSetML]);


val ntderive_firstset1 = store_thm("ntderive_firstset1",
  ``∀sn. ntderive g tok ns ∧ ALL_DISTINCT ns ∧
         (IMAGE NTS (set ns) ∩ set sn = {}) ⇒
         MEM (TS tok) (firstSetML g sn [NTS (HD ns)])``,
  Induct_on `ns` THEN
  SRW_TAC [][firstSetML, rmDupes, LET_THM, rmd_mem_list] THENL [
    DISJ2_TAC THEN DISJ2_TAC THEN
    SRW_TAC [boolSimps.DNF_ss][EXTENSION],

    Cases_on `ns` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [boolSimps.DNF_ss][MEM_FLAT, MEM_MAP] THEN
      Q.EXISTS_TAC `pfx ++ [TS tok] ++ sfx` THEN
      SRW_TAC [][MEM_getRhs] THEN
      `MEM (TS tok) (firstSetML g (NTS h::sn) ([TS tok] ++ sfx))`
         by SRW_TAC [][firstSetML] THEN
      METIS_TAC [APPEND_ASSOC, firstset1_nullable_append],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [boolSimps.DNF_ss][MEM_FLAT, MEM_MAP] THEN
      Q.EXISTS_TAC `pfx ++ [NTS h'] ++ sfx` THEN
      SRW_TAC [][MEM_getRhs] THEN
      ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN
      MATCH_MP_TAC firstset1_nullable_append THEN
      SRW_TAC [][] THEN MATCH_MP_TAC firstset1_cons_I THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SRW_TAC [][] THEN
      POP_ASSUM MP_TAC THEN
      SRW_TAC [][EXTENSION] THEN
      METIS_TAC [symbol_11]
    ]
  ]);

val nullable_NIL = store_thm(
  "nullable_NIL",
  ``nullable g []``,
  SRW_TAC [][nullable_def])
val _ = export_rewrites ["nullable_NIL"];

Theorem split_killer:
  ∀y p s.
    (x ++ y = p ++ [E] ++ s) <=>
    (∃x2. (x = p ++ [E] ++ x2) ∧ (s = x2 ++ y)) ∨
    (∃y1. (p = x ++ y1) ∧ (y = y1 ++ [E] ++ s))
Proof
  Induct_on `x` THEN SRW_TAC [][] THEN
  Cases_on `p` THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
  METIS_TAC []
QED

val isolate_last = store_thm
("isolate_last",
  ``∀l e. MEM e l ⇒
          ∃pfx sfx. (l = pfx ++ [e] ++ sfx) ∧
                    ¬MEM e sfx``,
  Induct THEN SRW_TAC [][] THEN METIS_TAC [APPEND]);



Theorem ntderive_list_exists:
  ∀sf1 sf2.
       (derives g)^* sf1 sf2 ⇒
       ∀tok rest. sf2 = TS tok :: rest ∧
                  (∀pfx sfx. nullable g pfx ⇒
                             sf1 ≠ pfx ++ [TS tok] ++ sfx)
                 ⇒
                  ∃nlist pfx sfx.
                     (sf1 = pfx ++ [NTS (HD nlist)] ++ sfx) ∧
                     nullable g pfx ∧
                     ntderive g tok nlist ∧
                     ALL_DISTINCT nlist
Proof
  HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
    (POP_ASSUM (Q.SPEC_THEN `[]` MP_TAC) THEN
		SRW_TAC [][] THEN
		FULL_SIMP_TAC (srw_ss()) [nullable_def]) THEN
  `∃N rhs pfx sfx.
      MEM (rule N rhs) (rules g) ∧
      (sf1 = pfx ++ [NTS N] ++ sfx) ∧
      (sf1' = pfx ++ rhs ++ sfx)`
     by METIS_TAC [derives_def] THEN
  SRW_TAC [][] THEN
  Cases_on `∀p s. nullable g p ⇒
                  ¬(pfx ++ rhs ++ sfx = p ++ [TS tok] ++ s)`
  THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (Q.PAT_X_ASSUM `∀x. P x` (K ALL_TAC)) THEN
    RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [split_killer]) THEN
    FULL_SIMP_TAC (srw_ss()) [] THENL [
      SRW_TAC [][] THEN METIS_TAC [APPEND_ASSOC],
      SRW_TAC [][] THEN
      Cases_on `MEM N nlist` THENL [
        `∃n0 nsfx. (nlist = n0 ++ [N] ++ nsfx) ∧
                   ¬ MEM N nsfx`
           by METIS_TAC [isolate_last] THEN
        SRW_TAC [][] THEN
        MAP_EVERY Q.EXISTS_TAC
                  [`N :: nsfx`, `pfx`, `sfx`] THEN
        SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss()) [nullable_APPEND],
          METIS_TAC [ntderive_APPEND, APPEND_ASSOC, APPEND,
                     NOT_CONS_NIL],
          METIS_TAC [ALL_DISTINCT_APPEND]
        ],

	MAP_EVERY Q.EXISTS_TAC
                  [`N :: nlist`, `pfx`, `sfx`] THEN
        SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss()) [nullable_APPEND],
	  Cases_on `nlist` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	  METIS_TAC [nullable_APPEND]
        ]
      ],

      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC
		[`nlist`, `pfx ++ [NTS N] ++ y1`, `sfx'`] THEN
      SRW_TAC [][] THEN
      METIS_TAC [nullable_APPEND, nullable_def, res1,
		 RTC_RULES]
    ],

    FULL_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM (MP_TAC o SIMP_RULE (srw_ss()) [split_killer]) THEN
    STRIP_TAC THEN SRW_TAC [][] THENL [
      METIS_TAC [APPEND_ASSOC],
      MAP_EVERY Q.EXISTS_TAC [`[N]`, `pfx`, `sfx`] THEN
      SRW_TAC [][] THEN METIS_TAC [nullable_APPEND],
      `nullable g [NTS N]`
         by METIS_TAC [nullable_APPEND, RTC_RULES, res1,
		       nullable_def] THEN
      FULL_SIMP_TAC (srw_ss()) [nullable_APPEND] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`pfx ++ [NTS N] ++ y1`, `s`]
				  MP_TAC) THEN
      SRW_TAC [][nullable_APPEND]
    ]
  ]
QED

Theorem lemma =  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) []
		           ntderive_list_exists

val first_first1 = store_thm("first_first1",
  ``TS t ∈ firstSetList g sf ⇒ TS t ∈ set (firstSetML g [] sf)``,
  SRW_TAC [][firstSetList] THEN
  Cases_on `∀p s. nullable g p ⇒ ¬(sf = p ++ [TS t] ++ s)` THENL[
    `∃nlist pfx sfx.
        (sf = pfx ++ [NTS (HD nlist)] ++ sfx) ∧
        nullable g pfx ∧ ntderive g t nlist ∧
        ALL_DISTINCT nlist`
      by METIS_TAC [lemma] THEN
    SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN
    MATCH_MP_TAC firstset1_nullable_append THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC firstset1_cons_I THEN
    MATCH_MP_TAC ntderive_firstset1 THEN
    SRW_TAC [][],

    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN
    MATCH_MP_TAC firstset1_nullable_append THEN
    SRW_TAC [][firstSetML]
  ]);



val firstSetMLEq = store_thm ("firstSetMLEq",
``∀g l.((MEM s (firstSetML g [] l)) =
             (s ∈ (firstSetList g l)))``,
SRW_TAC [] [EQ_IMP_THM]
THENL[
      METIS_TAC [firstSetMLEq1],

      `∃ts.s=TS ts`
	  by (Cases_on `s` THEN
	      FULL_SIMP_TAC (srw_ss()) [firstSetList]) THEN
      SRW_TAC [][] THEN
      METIS_TAC [first_first1,containerLemmasTheory.mem_in]
      ]);



(*
val _ = save_thm ("firstSetML",firstSetML);
val _ = save_thm ("firstSetML_ind",firstSetML_ind);

val _ = save_thm ("firstSetML",firstSetML);
val _ = save_thm ("firstSetML_ind",firstSetML_ind);
*)

val followML_defn = Hol_defn "followML"
  `(followG g sn N = followrs g sn N (rules g)) ∧
   (followrs g sn N [] = {}) ∧
   (followrs g sn N (r::rs) =
      followr g sn N (ruleLhs r) (ruleRhs r) ∪
      followrs g sn N rs) ∧
   (followr g sn N M [] = {}) ∧
   (followr g sn N M (TS t::rest) = followr g sn N M rest) ∧
   (followr g sn N M (NTS P :: rest) =
      (if N = P then
         firstSetList g rest ∪
         (if nullableML g [] rest then
            if M ∈ sn ∨ (* NTS M ∉ nonTerminals g ∨ *)
               ¬(IMAGE NTS (set sn) ⊆ nonTerminals g) then {}
            else followG g (N::sn) M
          else {})
       else {}) ∪ followr g sn N M rest)`


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
    :: DEFN firstSetML
    :: DEFN firstSetMLList
    :: [])
 end;
*)


val _ = export_theory ();
