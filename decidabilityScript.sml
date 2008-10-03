open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
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
	         (p=p') \/ ~okPfx g p'`

val maxPfxExists =
store_thm ("maxPfxExists",
``(auggr g st eof = SOME ag) ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
!s.?pfx sfx sfx'.maxPfx g pfx s /\ (s=pfx++sfx)
/\ (pfx++sfx') IN (language ag)``,
MAGIC)



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


