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
    inv_image (measure (λ(g,sn). CARD ((nonTerminals g) DIFF
                                 (LIST_TO_SET sn)))
                LEX
               measure (λ(syms).LENGTH syms))
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
    `(NTS N) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `~((NTS N) IN set sn)` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
    `~(NTS N IN (nonTerminals g INTER set sn))` by METIS_TAC [IN_INTER] THEN
    `~(nonTerminals g = set sn)` by METIS_TAC [] THEN
    `FINITE (nonTerminals g)`
       by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
    `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
    `FINITE (NTS N INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
    `CARD (nonTerminals g) - CARD (nonTerminals g ∩ set sn) =
       CARD ((nonTerminals g) DIFF (set sn))` by METIS_TAC [CARD_DIFF] THEN
    ASM_REWRITE_TAC [] THEN
    `(NTS N) ∈ (nonTerminals g DIFF set sn)`
       by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
    `~((nonTerminals g DIFF set sn)={})` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
    `~(CARD (nonTerminals g DIFF set sn)=0)`
       by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
    DECIDE_TAC
  ])

val _  = export_theory()

