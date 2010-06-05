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
          ∃pfx sfx.RTC (derives g) s (pfx++[sym]++[TS ts]++sfx) }`;


val followML_defn = Hol_defn "followML"
  `(followG g sn N = followrs g sn N (LENGTH (rules g) - 1)) ∧
   (followrs g sn N 0 = 
    followr g sn N 0 (LENGTH (ruleRhs (EL 0 (rules g))))) ∧
   (followrs g sn N i =
      followr g sn N i (LENGTH (ruleRhs (EL i (rules g)))) ∪
      followrs g sn N (i - 1)) ∧
   (followr g sn N i 0 = {}) ∧
   (followr g sn N i rhsLen = 
    case (TAKE rhsLen (ruleRhs (EL i (rules g)))) of
       (TS t::rest) -> followr g sn N i (rhsLen - 1) 
    || (NTS P :: rest) ->
      (if N = P then
         firstSetList g rest ∪
         (if nullableML g [] rest then
            if  N ∈ sn then {}
            else followG g (N::sn) (ruleLhs (EL i (rules g)))
          else {})
       else {}) ∪ followr g sn N i (rhsLen - 1))`;


val easy_def = Define`
  (easy (INL _) = 0) ∧
  (easy (INR (INL (_, _, _, i))) = i) ∧
  (easy (INR (INR (_, _, _, _, i))) = i)
`;

val cg_def = Define`
  (cg (INL _) = 2) ∧
  (cg (INR (INL _)) = 1) ∧
  (cg (INR (INR _)) = 0)
`;


val validSeen = Define 
`validSeen (g:(α, β) grammar) (sn:α list) = 
{ (NTS e):(α, β) symbol | MEM e sn ∧ NTS e ∈ nonTerminals g }`;

val tricky_def = Define`
  tricky (g,sn) = CARD (nonTerminals g) - CARD (validSeen g sn)
  `;

val gsn_def = Define`
  (gsn (INL (g,sn,_)) = (g,sn)) ∧
  (gsn (INR (INL (g,sn,_))) = (g,sn)) ∧
  (gsn (INR (INR (g,sn,_))) = (g,sn))`



val takeMem = store_thm
("takeMem",
``∀l l' n.(TAKE n l = l') ⇒ (∀e. e ∈ l' ⇒ e ∈ l)``,

Induct_on `l` THEN SRW_TAC [][] THEN1
METIS_TAC [MEM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [TAKE_def] THEN
METIS_TAC [MEM]);


tgoal followML_defn

``∀i l. (EL i l = x) ⇒ x ∈ l``



``NTS P ∈ ruleRhs (EL i (rules g)) ⇒ NTS P ∈ nonTerminals g``,

SRW_TAC [][] THEN
Cases_on `EL i (rules g)` THEN
FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
METIS_TAC [slemma1_4, rgr_r9eq, ]

val (followML_def, followML_ind) = tprove(
  followML_defn,
  WF_REL_TAC `inv_image (measure tricky LEX $< LEX measure easy)
                        (λx. (gsn x, cg x, x))` THEN
  SRW_TAC [][gsn_def, cg_def, easy_def, tricky_def] THEN

`NTS P ∈ ruleRhs (EL i (rules g))` by METIS_TAC [MEM, takeMem] THEN
`NTS P ∈ nonTerminals g` by MAGIC THENL[
SRW_TAC [][validSeen] THEN
`{e | ((e = P) ∨ e ∈ sn) ∧ NTS e ∈ nonTerminals g} =
{P} ∪ {e | e ∈ sn ∧ NTS e ∈ nonTerminals g}` by (SRW_TAC [][EXTENSION] THEN
						 METIS_TAC []) THEN
`{P} ∩ {e | e ∈ sn ∧ NTS e ∈ nonTerminals g} = {}`
by (SRW_TAC [][EXTENSION] THEN METIS_TAC []) THEN
`FINITE {e | e ∈ sn ∧ NTS e ∈ nonTerminals g}` by MAGIC THEN
`CARD {e | ((e = P) ∨ e ∈ sn) ∧ NTS e ∈ nonTerminals g} + 0 =
CARD {P} + CARD {e | e ∈ sn ∧ NTS e ∈ nonTerminals g}` by 
			  METIS_TAC [CARD_UNION,FINITE_SING,
				     FINITE_LIST_TO_SET,CARD_EMPTY] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
DECIDE_TAC,

Q_TAC SUFF_TAC `CARD (validSeen g sn) < CARD (nonTerminals g)` THEN1
DECIDE_TAC THEN
`FINITE (nonTerminals g)` by MAGIC THEN
Q_TAC SUFF_TAC `validSeen g sn ⊂ nonTerminals g` THEN1 METIS_TAC [CARD_PSUBSET]

`FINITE (validSeen g sn)`
``




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
  Q.EXISTS_TAC `s'` THEN SRW_TAC [][] THEN
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


val followSetMem = store_thm 
("followSetMem", 
``∀u v.RTC (derives g) u v ⇒ (u=[NTS N]) ⇒
(v=(pfx++[NTS N']++[TS ts]++sfx)) ⇒
((TS ts) IN followSet g (NTS N'))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN1
 FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
 FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq, followSet] THEN
 Q.EXISTS_TAC `u'` THEN
 SRW_TAC [] [] 
 THENL[
       FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN
       METIS_TAC [],
			  
       METIS_TAC []]);



val ntderive'_def = Define`
  (ntderive' g tok [] = F) ∧ 
  (ntderive' g tok [N] = 
     ∃pfx sfx rhs. 
        MEM (rule N rhs) (rules g) ∧
        (rhs = pfx ++ [tok] ++ sfx) ∧
        nullable g pfx) ∧
  (ntderive' g tok (N1 :: N2 :: Ns) = 
     ∃pfx sfx rhs.
        MEM (rule N1 rhs) (rules g) ∧
        (rhs = pfx ++ [NTS N2] ++ sfx) ∧
        nullable g pfx ∧
        ntderive' g tok (N2 :: Ns))
`;

val _ = export_rewrites ["ntderive'_def"];

val ntderive'_APPEND = store_thm(
  "ntderive'_APPEND",
  ``∀l1 l2. ntderive' g tok (l1 ++ l2) ∧ ¬(l2 = []) ⇒
            ntderive' g tok l2``,
  Induct THEN1 SRW_TAC [][] THEN 
  Cases_on `l1` THEN SRW_TAC [][] THENL [
    Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [APPEND]
  ]);

val ntderive'_list_exists = prove(
  ``∀sf1 sf2.
       (derives g)^* sf1 sf2 ⇒
       ∀tok rest. (sf2 = tok :: rest) ∧
                  (∀pfx sfx. nullable g pfx ⇒ 
                             ¬(sf1 = pfx ++ [tok] ++ sfx))
                 ⇒ 
                  ∃nlist pfx sfx. 
                     (sf1 = pfx ++ [NTS (HD nlist)] ++ sfx) ∧
                     nullable g pfx ∧
                     ntderive' g tok nlist ∧ 
                     ALL_DISTINCT nlist``,      
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
                  ¬(pfx ++ rhs ++ sfx = p ++ [tok] ++ s)`
  THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (Q.PAT_ASSUM `∀x. P x` (K ALL_TAC)) THEN 
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
          METIS_TAC [ntderive'_APPEND, APPEND_ASSOC, APPEND,
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
  ]);

val lemma' =  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] 
		       ntderive'_list_exists 


(*
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


``∀g sn sf. ts ∈ firstSet1 g sn sf ⇒ ts ∈ followSet ``
*)

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