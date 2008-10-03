open HolKernel boolLib Parse bossLib

open regexpTheory grammarDefTheory
open firstSetDefTheory listLemmasTheory
open containerTheory pred_setTheory listTheory

val _ = new_theory "firstMLAcc"

val _ = set_trace "Unicode" 1

val firstSetAML_defn = Hol_defn "firstSetAML" `
  (firstSetAML g acc sn [] = acc) ∧
  (firstSetAML g acc sn (sym :: rest) =
     case sym of
        TS t -> sym INSERT acc
     || NTS N -> let
                  acc' = if nullableML g [][sym] then firstSetAML g acc sn rest
                         else acc
        in
          if MEM sym sn then acc'
          else
            FOLDL (λacc rhs. firstSetAML g acc (sym::sn) rhs)
                  acc'
                  (getRhs N (rules g)))
`;

val (firstSetAML_def, firstSetAML_ind) = Defn.tprove(
  firstSetAML_defn,
  WF_REL_TAC `
    inv_image (measure (λ(g,sn). CARD (nonTerminals g DIFF LIST_TO_SET sn))
                LEX
               measure LENGTH)
              (λ(g,acc,sn,syms).((g,sn),syms))` THEN
  SRW_TAC [] [] THEN
  `FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
  `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
  `FINITE (NTS A INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
  SRW_TAC [][CARD_DIFF] THENL [
    `~(getRhs N (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `(NTS N) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `(nonTerminals g ∩ (NTS N INSERT set sn)) =
     (NTS N INSERT set sn) ∩ nonTerminals g`
       by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
    SRW_TAC [] [arithmeticTheory.ADD1] THEN
    `(nonTerminals g INTER set sn) = (set sn INTER nonTerminals g)`
      by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    DECIDE_TAC,

    `~(getRhs N (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `NTS N ∈ nonTerminals g` by METIS_TAC [ntsInGr] THEN
    `~(NTS N ∈ set sn)` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
    `~(NTS N ∈ nonTerminals g ∩ set sn)` by METIS_TAC [IN_INTER] THEN
    `~(nonTerminals g = set sn)` by METIS_TAC [] THEN
    `FINITE (nonTerminals g)`
       by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
    `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
    `FINITE (NTS N INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
    `CARD (nonTerminals g) - CARD (nonTerminals g ∩ set sn) =
       CARD ((nonTerminals g) DIFF (set sn))` by METIS_TAC [CARD_DIFF] THEN
    ASM_REWRITE_TAC [] THEN
    `NTS N ∈ nonTerminals g DIFF set sn`
       by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
    `~(nonTerminals g DIFF set sn = {})` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
    `~(CARD (nonTerminals g DIFF set sn)=0)`
       by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
    DECIDE_TAC
  ])

open relationTheory
val RTC_derives_tokfirst = store_thm(
  "RTC_derives_tokfirst",
  ``(derives g)^* (TS tok::rest) y =
    ∃rest'. (y = TS tok :: rest') ∧ (derives g)^* rest rest'``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC
      `∀x y. (derives g)^* x y ⇒
             ∀tok t. (x = TS tok :: t) ⇒
                        ∃t'. (y = TS tok :: t') ∧ (derives g)^* t t'`
      THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THEN
    `∃pfx N sfx rhs. (TS tok :: t = pfx ++ [NTS N] ++ sfx) ∧
                     (x' = pfx ++ rhs ++ sfx) ∧
                     MEM (rule N rhs) (rules g)`
        by METIS_TAC [derives_def] THEN
    SRW_TAC [][] THEN
    `∃p'. (pfx = TS tok :: p')` by (Cases_on `pfx`  THEN
                                    FULL_SIMP_TAC (srw_ss()) []) THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [derives_def, RTC_RULES],

    SRW_TAC [][] THEN METIS_TAC [rtc_derives_same_append_left, APPEND]
  ]);


val firstSetList_TS = store_thm(
  "firstSetList_TS",
  ``firstSetList g (TS tok :: rest) = {TS tok}``,
  SRW_TAC [boolSimps.DNF_ss]
          [firstSetList_def, RTC_derives_tokfirst, EXTENSION] THEN
  METIS_TAC [RTC_RULES]);
val _ = export_rewrites ["firstSetList_TS"]

val firstSetList_nullable_cons = store_thm(
  "firstSetList_nullable_cons",
  ``t ∈ firstSetList g sf ∧ nullable g [NTS N] ⇒
    t ∈ firstSetList g (NTS N :: sf)``,
  SRW_TAC [][firstSetList_def, nullable_def] THEN
  METIS_TAC [derives_append, APPEND]);

val firstSetList_expand_rule = store_thm(
  "firstSetList_expand_rule",
  ``t ∈ firstSetList g r ∧ MEM (rule N r) (rules g) ⇒
    t ∈ firstSetList g (NTS N :: rest)``,
  SRW_TAC [][firstSetList_def] THEN
  METIS_TAC [derives_def, APPEND, RTC_RULES, rtc_derives_same_append_right]);

val accumulatingset_FOLDL = prove(
  ``∀l a b.
      (∀e a b. MEM e l ⇒ (f (a ∪ b) e = f a e ∪ b)) ⇒
      (FOLDL f (a ∪ b) l = FOLDL f a l ∪ b)``,
  Induct THEN SRW_TAC [][]);

val firstSetAML_acc = store_thm(
  "firstSetAML_acc",
  ``∀g a sn r b. firstSetAML g (a ∪ b) sn r = firstSetAML g a sn r ∪ b``,
  HO_MATCH_MP_TAC firstSetAML_ind THEN
  SIMP_TAC (srw_ss()) [firstSetAML_def] THEN REPEAT GEN_TAC THEN
  `(∃tok. sym = TS tok) ∨ (∃N. sym = NTS N)`
      by (Cases_on `sym` THEN SRW_TAC [][]) THEN
  SRW_TAC [][LET_THM] THENL [
    SRW_TAC [][EXTENSION] THEN METIS_TAC [],
    MATCH_MP_TAC accumulatingset_FOLDL THEN METIS_TAC [],
    MATCH_MP_TAC accumulatingset_FOLDL THEN METIS_TAC []
  ]);

val firstSetAML_FOLDL = prove(
  ``∀l acc.
       ¬(t ∈ acc) ⇒
       t ∈ FOLDL (λa r. firstSetAML g a sn r) acc l
      ⇒
       ∃r. MEM r l ∧ ∀a'. t ∈ firstSetAML g a' sn r``,
  Induct THEN SRW_TAC [][] THEN
  Cases_on `t ∈ firstSetAML g acc sn h` THENL [
    METIS_TAC [UNION_EMPTY, UNION_COMM, IN_UNION, firstSetAML_acc],
    METIS_TAC []
  ]);

val MEM_getRhs = store_thm(
  "MEM_getRhs",
  ``MEM r (getRhs N l) = MEM (rule N r) l``,
  Induct_on `l` THEN SRW_TAC [][getRhs_def] THEN
  Cases_on `h` THEN SRW_TAC [][getRhs_def] THEN SRW_TAC [][]);

val firstSetAML_firstSetList = store_thm(
  "firstSetAML_firstSetList",
  ``∀g acc sn sf t.
        t ∈ firstSetAML g acc sn sf ⇒ t ∈ acc ∨ t ∈ firstSetList g sf``,
  HO_MATCH_MP_TAC firstSetAML_ind THEN
  SIMP_TAC (srw_ss()) [firstSetAML_def] THEN
  REPEAT GEN_TAC THEN
  `(∃tok. sym = TS tok) ∨ (∃N. sym = NTS N)`
       by (Cases_on `sym` THEN SRW_TAC [][]) THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [] THEN
  Cases_on `MEM (NTS N) sn` THEN1
    (SRW_TAC [][LET_THM] THEN
     METIS_TAC [firstSetList_nullable_cons, nullableEq]) THEN
  ASM_SIMP_TAC (srw_ss()) [LET_THM] THEN
  SRW_TAC [][] THENL [
    Cases_on `t ∈ firstSetAML g acc sn sf` THEN1
      METIS_TAC [firstSetList_nullable_cons, nullableEq] THEN
    `∃r. MEM r (getRhs N (rules g)) ∧
         ∀a'. t ∈ firstSetAML g a' (NTS N::sn) r`
       by METIS_TAC [firstSetAML_FOLDL] THEN
    `t ∈ firstSetList g r` by METIS_TAC [NOT_IN_EMPTY] THEN
    METIS_TAC [firstSetList_expand_rule, MEM_getRhs],

    Cases_on `t ∈ acc` THEN SRW_TAC [][] THEN
    `∃r. MEM r (getRhs N (rules g)) ∧
         ∀a'. t ∈ firstSetAML g a' (NTS N::sn) r`
      by METIS_TAC [firstSetAML_FOLDL] THEN
    `t ∈ firstSetList g r` by METIS_TAC [NOT_IN_EMPTY] THEN
    METIS_TAC [firstSetList_expand_rule, MEM_getRhs]
  ]);

val _  = export_theory()

