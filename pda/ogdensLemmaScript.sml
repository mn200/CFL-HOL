open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory


open listLemmasTheory relationLemmasTheory grammarDefTheory
     arithmeticLemmasTheory symbolDefTheory cnfTheory parseTreeTheory
     treeDerivTheory containerLemmasTheory pumpingLemmaTreeTheory

val _ = new_theory "ogdensLemma";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

val marked = Define
`marked P l = LENGTH (FILTER P l)`;

val maxSp = Define
`(maxSp P (Leaf ts) = []) ∧
(maxSp P (Node nt [t1]) = []) ∧
 (maxSp P (Node nt [t1;t2]) = 
  if (marked P (leaves t1) ≤ marked P (leaves t2)) 
      then 1::maxSp P t2
  else 0::maxSp P t1)`;


val countDistLeaves = Define
`(countDistLeaves P (Leaf ts)  = []) ∧
 (countDistLeaves P (Node nt stl) = MAP (marked P) (MAP leaves stl))`;

val branchPoints = Define
`(branchPoints P [] t = []) ∧
(branchPoints P (p::path) (Node nt [Node n1 t1; Node n2 t2]) = 
 if (LENGTH (FILTER (λn. n = 0) 
	     (countDistLeaves P (Node nt [Node n1 t1; Node n2 t2]))) = 0)
     then (Node nt [Node n1 t1; Node n2 t2])::
	 branchPoints P path (EL p [Node n1 t1; Node n2 t2])
 else branchPoints P path (EL p [Node n1 t1; Node n2 t2])) ∧
 (branchPoints P path t = [])`;


val markedApp = store_thm
("markedApp",
``∀l1 l2. marked P (l1 ++ l2) = marked P l1 + marked P l2``,

Induct_on `l1` THEN SRW_TAC [][marked] THEN
FULL_SIMP_TAC (srw_ss()) [marked, FILTER_APPEND] THEN
DECIDE_TAC);


val bpImpMarked = store_thm
("bpImpMarked",
``∀g t. validptree g t ⇒ isCnf g ⇒ 
∀k. LENGTH (branchPoints P (maxSp P t) t) ≤ k ⇒
marked P (leaves t) ≤ 2**k``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] 
THENL[
      IMP_RES_TAC cnfTree THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THENL[

      FULL_SIMP_TAC (srw_ss()) [maxSp] THEN
      Cases_on `marked P (leaves (Node n1 t1)) ≤ marked P (leaves (Node n2 t2))` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN1
      (`validptree g (Node n2 t2)` by 
       FULL_SIMP_TAC (srw_ss()) [validptree, isNode_def] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`Node n2 t2`] MP_TAC) THEN 
       SRW_TAC [][isNode_def] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`k`] MP_TAC) THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
      Cases_on `LENGTH
      (FILTER (λn. n = 0)
       (countDistLeaves P
	(Node n [Node n1 t1; Node n2 t2]))) = 0` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH
      (branchPoints P (maxSp P (Node n2 t2))
       (Node n2 t2)) ≤ k` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
      FULL_SIMP_TAC (srw_ss()) [markedApp] THEN DECIDE_TAC
      MAGIC) THEN

      (`validptree g (Node n1 t1)` by 
       FULL_SIMP_TAC (srw_ss()) [validptree, isNode_def] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`Node n1 t1`] MP_TAC) THEN 
       SRW_TAC [][isNode_def] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`k`] MP_TAC) THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
      Cases_on `LENGTH
      (FILTER (λn. n = 0)
       (countDistLeaves P
	(Node n [Node n1 t1; Node n2 t2]))) = 0` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH
      (branchPoints P (maxSp P (Node n1 t1))
       (Node n1 t1)) ≤ k` by DECIDE_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
      MAGIC),

      FULL_SIMP_TAC (srw_ss()) [validptree, branchPoints, maxSp,
				leaves_def, marked] THEN
      SRW_TAC [][] THEN
      MAGIC],

      FULL_SIMP_TAC (srw_ss()) [validptree]
      ]);


val validCnfPath = Define `validCnfPath p = ∀e. e ∈ p ⇒ (e=0) ∨ (e=1)`;

(*
``∀g t. validptree g t ⇒ isCnf g ⇒
∀bps p. (bps = (branchPoints P p t)) ⇒ 
validCnfPath p ⇒
∀i. i < LENGTH bps ⇒ 
(∀j. j > i ∧ j < LENGTH bps ⇒ isSubtree (EL j bps) (EL i bps))``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] THENL[

IMP_RES_TAC cnfTree THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

Cases_on `i` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [validCnfPath] THEN
`(h = 0) ∨ (h=1)` by METIS_TAC [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1

`validptree g (Node n1 t1)` by FULL_SIMP_TAC (srw_ss()) [validptree, isNode_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`Node n1 t1`] MP_TAC) THEN SRW_TAC [][isNode_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`t`] MP_TAC) THEN SRW_TAC [][] THEN
Cases_on `j` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`n'`] MP_TAC) THEN SRW_TAC [][] THEN
SRW_TAC [][isSubtree_def]


Cases_on `j` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

*)


val memBpsSubEq = store_thm
("memBpsSubEq",
``∀g t. validptree g t ⇒ isCnf g ⇒
∀p. validCnfPath p ⇒
∀bps. (bps = (branchPoints P p t)) ⇒ 
∀e. e ∈ bps ⇒ isSubtreeEq e t``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][]
THENL[
      IMP_RES_TAC cnfTree THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `LENGTH
          (FILTER (λn. n = 0)
             (countDistLeaves P
                (Node n [Node n1 t1; Node n2 t2]))) =
        0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN1
      METIS_TAC [isSubEqImpSub] THEN
      (FULL_SIMP_TAC (srw_ss()) [validCnfPath] THEN
      `(h = 0) ∨ (h=1)` by METIS_TAC [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] 
      THENL[
	    `validptree g (Node n1 t1)` 
	    by FULL_SIMP_TAC (srw_ss()) [validptree, isNode_def] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`Node n1 t1`] MP_TAC) THEN
	    SRW_TAC [][isNode_def] THEN
	    `isSubtreeEq e (Node n1 t1)` by METIS_TAC [] THEN
	    `isSubtree (Node n1 t1) (Node n [Node n1 t1; Node n2 t2])` by
	    (SRW_TAC [][isSubtree_def] THEN
	     Q.EXISTS_TAC `[0]` THEN SRW_TAC [][subtree_def]) THEN
	    METIS_TAC [isSubEqImpSub, subtreeTrans],

	    `validptree g (Node n2 t2)` 
	    by FULL_SIMP_TAC (srw_ss()) [validptree, isNode_def] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`Node n2 t2`] MP_TAC) THEN
	    SRW_TAC [][isNode_def] THEN
	    `isSubtreeEq e (Node n2 t2)` by METIS_TAC [] THEN
	    `isSubtree (Node n2 t2) (Node n [Node n1 t1; Node n2 t2])` by
	    (SRW_TAC [][isSubtree_def] THEN
	     Q.EXISTS_TAC `[1]` THEN SRW_TAC [][subtree_def]) THEN
	    METIS_TAC [isSubEqImpSub, subtreeTrans]
	    ]),

      FULL_SIMP_TAC (srw_ss()) [validptree]
      ]);


val bpsApp = store_thm
("bpsApp",
``∀bps p t. (bps = (branchPoints P p t)) ⇒ bps ≠ [] ⇒
validCnfPath p ⇒
∃pfx sfx st. (p = pfx ++ sfx) ∧ (subtree t pfx = SOME st) ∧
(bps = branchPoints P pfx t ++ branchPoints P sfx st)``,

Induct_on `p` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
`∃n n1 t1 n2 t2. (t = Node n [Node n1 t1; Node n2 t2])` by MAGIC THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(Q.EXISTS_TAC `[]` THEN
Q.EXISTS_TAC `h::p` THEN
FULL_SIMP_TAC (srw_ss()) [branchPoints]) THEN

`validCnfPath p` by METIS_TAC [validCnfPath, MEM] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h [Node n1 t1; Node n2 t2]`] MP_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validCnfPath] THEN
`h < 2` by (`(h = 0) ∨ (h = 1)` by METIS_TAC [] THEN
	    DECIDE_TAC) THEN
Q.EXISTS_TAC `h::pfx` THEN
Q.EXISTS_TAC `sfx` THEN
Q.EXISTS_TAC `st` THEN
FULL_SIMP_TAC (srw_ss()) [subtree_def] THEN
FULL_SIMP_TAC (srw_ss()) [branchPoints]);


val bpsApp = store_thm
("bpsApp",
``∀bps p t. (bps = (branchPoints P p t)) ⇒ bps ≠ [] ⇒
validCnfPath p ⇒
 ((∃i st. (subtree t [i] = SOME st) ∧ (bps = t :: branchPoints P (TL p) st)) ∨
  (∃pfx sfx st. (pfx ≠ []) ∧ (p = pfx ++ sfx) ∧ (subtree t pfx = SOME st) ∧
   (bps = st :: branchPoints P  sfx st)))``,

completeInduct_on `ptheight t` THEN
SRW_TAC [][] THEN
`∃n n1 t1 n2 t2. (t = Node n [Node n1 t1; Node n2 t2])` by MAGIC THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`validCnfPath p` by METIS_TAC [validCnfPath, MEM] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
`(h = 0) ∨ (h = 1)` by METIS_TAC [validCnfPath, MEM] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN

FIRST_X_ASSUM (Q.SPECL_THEN [`ptheight (Node n1 t1)`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`Node n1 t1`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Cases_on `branchPoints P (0::t) (Node n1 t1) = []` THEN
SRW_TAC [][] THEN1





SRW_TAC [][] THEN1

DISJ1_TAC THEN
Q.EXISTS_TAC `[h]` THEN
Q.EXISTS_TAC `p` THEN
SRW_TAC [][]






(Q.EXISTS_TAC `[]` THEN
Q.EXISTS_TAC `h::p` THEN
SRW_TAC [][branchPoints] THEN
Q.EXISTS_TAC `h` THEN
Q.EXISTS_TAC `EL h [Node n1 t1; Node n2 t2]` THEN
SRW_TAC [][subtree_def] THEN
`h < 2` by (`(h = 0) ∨ (h = 1)` by METIS_TAC [validCnfPath, MEM] THEN
	    DECIDE_TAC)) THEN









``∀bps p t. (bps = (branchPoints P p t)) ⇒ 
¬ (ALL_DISTINCT (MAP root bps)) ⇒
∃pfx m sfx t1 t2. (bps = pfx ++ [t1] ++ m ++ [t2] ++ sfx) ∧
rootRep t2 t1 ∧ (∀st. ¬rootRep st t2)``,

Induct_on `bps` THEN SRW_TAC [][] THEN

Cases_on `t` THEN Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [branchPoints] THEN
Cases_on `LENGTH
          (FILTER (λn. n = 0)
             (countDistLeaves P (Node n l))) =
        0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THENL[




FIRST_X_ASSUM (Q.SPECL_THEN [`t`,`EL h' l`] MP_TAC) THEN SRW_TAC [][] THEN
Cases_on `¬ALL_DISTINCT
         (MAP root (branchPoints P t (EL h' l)))` THEN1
METIS_TAC [APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
IMP_RES_TAC rgr_r9eq THEN
SRW_TAC [][rootRep_def] THEN
`isSubtreeEq y (EL h' l)` by METIS_TAC [memBpsSubEq] THEN
`isSubtree (EL h' l) (Node n l)`by MAGIC THEN
MAGIC



``∀bps. bps ≠ [] ⇒
(bps = branchPoints P (maxSp P t) t) ⇒ ALL_DISTINCT (MAP root bps) ⇒
      (∃ntl ntl1 ntl2. (LAST bps = Node ntl [ntl1;ntl2]) ∧
      ∃ntm pfx sfx. (bps = pfx ++ [ntm] ++ sfx) ∧ rootRep ntl1 ntm ∧
      ∀e. e ∈ sfx ⇒ root e ≠ root ntm)``

Induct_on `bps` THEN SRW_TAC [][] THEN
Cases_on `bps` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN







val ogdensLemma = store_thm
("ogdensLemma",
``∀g.
   isCnf (g:('a,'b) grammar)  ⇒
   ∃n. n > 0 ∧
       ∀z. z ∈ language g ∧ marked P (MAP tsToStr z) ≥ n ⇒
           ∃u v w x y.
             (z = u ++ v ++ w ++ x ++ y) ∧
             marked P (MAP ts2str (v++x)) ≥ 1 ∧
	     marked P (MAP ts2str (v++w++x)) ≤ n ∧
             ∀i. u ++ FLAT (lpow v i) ++ w ++ FLAT (lpow x i) ++ y ∈ language g``,

SRW_TAC [][] THEN
 Q.ABBREV_TAC `k=LENGTH (ntms g)` THEN
 Q.EXISTS_TAC `2**k + 1` THEN
SRW_TAC [][] THEN1
MAGIC THEN

`∃t. validptree g t ∧ (root t = NTS (startSym g)) ∧ (z = MAP TS (leaves t))` 
 by METIS_TAC [ptLangThm, fringeEqLeaves] THEN
SRW_TAC [][] THEN
Q.ABBREV_TAC `p = maxSp P t` THEN
Q.ABBREV_TAC `bps = branchPoints P (maxSp P t) t` THEN
`LENGTH bps ≥ k` by MAGIC THEN
Cases_on `ALL_DISTINCT (MAP root bps)`
THENL[
      `∃ntl ntl1 ntl2. (LAST bps = Node ntl [ntl1;ntl2]) ∧
      ∃ntm pfx sfx. (bps = pfx ++ [ntm] ++ sfx) ∧ rootRep ntl1 ntm ∧
      ∀e. e ∈ sfx ⇒ root e ≠ root ntm` by MAGIC THEN
      SRW_TAC [][] THEN
      
      




      ]


val _ = export_theory ();