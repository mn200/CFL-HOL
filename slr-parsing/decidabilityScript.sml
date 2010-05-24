open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
parserDefTheory yaccDefTheory parseProp1DefTheory parseProp2DefTheory
lrGrammarDefTheory validItemInvTheory macStepTheory complDefTheory


fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w) 

val _ = Globals.linewidth := 60


val pfxProp = store_thm ("pfxProp",
``(auggr g st eof = SOME ag) ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
!s.?pfx sfx sfx'.(s=pfx++sfx)
/\ (pfx++sfx') IN (language ag)``,
MAGIC)

val okPfx = 
Define `okPfx g p = ?sfx.(p++sfx) IN (language g)`

val maxPfx = Define
`maxPfx g p s = ?sf.okPfx g p /\ (p++sf = s)
	         /\ (!p'.IS_PREFIX p' p ==> 
	                (p=p') \/ ~okPfx g p')`

val maxPfxExists =
store_thm ("maxPfxExists",
``(auggr g st eof = SOME ag) ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
!s.?pfx sfx sfx'.maxPfx g pfx s /\ (s=pfx++sfx)
/\ (pfx++sfx') IN (language ag)``,
MAGIC)


``(pfx++sfx) IN language g ==>
  ?p p'.(pfx=p++p') /\
  ?rst rhs lhs.handleg g pfx rhs (p',lhs,rst)``
SRW_TAC [] [language_def] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES2] 
THENL[
      MAGIC,

      FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
      SRW_TAC [] [] THEN
      `(s1++rhs = pfx) /\ (s2 = sfx) \/
       (?s1' s2'.
          (s1++rhs = pfx ++ s1') /\ (s2 = s2') /\
          (sfx = s1' ++ s2')) \/
       ?s1' s2'.
         (pfx = s1++rhs ++ s1') /\ (sfx = s2') 
       /\ (s2 = s1' ++ s2')`
	  by METIS_TAC [twoListAppEq] THEN
      SRW_TAC [][]
      THENL[

	    SRW_TAC [] [handleg_def]

]



``(auggr g st eof = SOME m) ==>
  (slr ag = SOME m) ==>
  (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
    ``



val treeNotExists = 
store_thm ("treeNotExists",
``(auggr g st eof = SOME ag) ==>
(slr ag = SOME m) ==>
EVERY isTmnlSym sl ==>
~(sl IN language ag) ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
(initState = (NTS st,initItems ag (rules ag))) ==>
(parser ag (SOME m) sl [] [initState] (TS eof)
           (NTS (startSym g)) = SOME NONE)``,

MAGIC)


