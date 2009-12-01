open HolKernel boolLib bossLib Parse
open boolLemmasTheory

val _ = new_theory "whileLemmas";

val owhile_def = Define`
owhile C f s = if ?n. ~ C (FUNPOW f n s) then
SOME (FUNPOW f (LEAST n. ~ C (FUNPOW f n s)) s)
else NONE
`;
val FUNPOW = arithmeticTheory.FUNPOW

val owhile_thm = store_thm(
"owhile_thm",
``owhile C f s = if C s then owhile C f (f s)
else SOME s``,
SRW_TAC [][owhile_def] THENL [
numLib.LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
numLib.LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
Q.MATCH_ABBREV_TAC `FUNPOW f N s = FUNPOW f M (f s)` THEN
Q_TAC SUFF_TAC `N = SUC M` THEN1 SRW_TAC [][FUNPOW] THEN
markerLib.RM_ALL_ABBREVS_TAC THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`(N = M) \/ (N < M) \/ (SUC M < N)` by DECIDE_TAC THENL [
SRW_TAC [][] THEN
`(M = 0) \/ ?M0. M = SUC M0`
by METIS_TAC [TypeBase.nchotomy_of ``:num``]
THEN1 FULL_SIMP_TAC (srw_ss()) [FUNPOW] THEN
FULL_SIMP_TAC (srw_ss()) [FUNPOW] THEN
METIS_TAC [DECIDE ``n < SUC n``],

`(N = 0) \/ ?N0. N = SUC N0`
by METIS_TAC [TypeBase.nchotomy_of ``:num``]
THEN1 FULL_SIMP_TAC (srw_ss()) [FUNPOW] THEN
`N0 < M` by DECIDE_TAC THEN
METIS_TAC [FUNPOW],
METIS_TAC [FUNPOW]
],
METIS_TAC [FUNPOW, TypeBase.nchotomy_of ``:num``],
numLib.LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
Cases_on `n'` THEN SRW_TAC [][FUNPOW] THEN
METIS_TAC [DECIDE ``0 < SUC n``, FUNPOW],

METIS_TAC [FUNPOW, TypeBase.nchotomy_of ``:num``],
METIS_TAC [FUNPOW, TypeBase.nchotomy_of ``:num``]
]);

val terminates_def = Define`terminates (C,f,s) = ?n. ~ C(FUNPOW f n s)`

val owhile_EQ_NONE = store_thm(
"owhile_EQ_NONE",
``(owhile C f s = NONE) = ~terminates (C, f, s)``,
SRW_TAC [][owhile_def, terminates_def] THEN METIS_TAC [])

val lemma = prove(
``!n s. (!x. P (f x) ==> P x) /\ P (FUNPOW f n s) ==> P s``,
Induct THEN SRW_TAC [][FUNPOW]);

val obua_induct2 = store_thm(
"obua_induct2",
``terminates (C, f, s) /\
(!x. (C x ==> P (f x)) ==> P x) ==>
P s``,
SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [terminates_def] THEN
Induct THEN SRW_TAC [][FUNPOW] THEN
Cases_on `C (FUNPOW f n s)` THENL [
METIS_TAC [lemma],
METIS_TAC []
]);

val owhile_EQ_SOME = store_thm(
"owhile_EQ_SOME", 
``(?s'.owhile C f s = SOME s') = terminates (C, f, s)``,
SRW_TAC [] [EQ_IMP_THM] THEN
 METIS_TAC [optionTheory.NOT_SOME_NONE,optionTheory.option_nchotomy,owhile_EQ_NONE])

val owhileEndCond = store_thm ("owhileEndCond", 
``!s'.(owhile C f s = SOME s') ==> ~ C s'``,
FULL_SIMP_TAC (srw_ss()) [owhile_def,owhile_EQ_SOME,if_rw_SOMEeqSOME] THEN
STRIP_TAC THEN
numLib.LEAST_ELIM_TAC THEN SRW_TAC [][] THEN METIS_TAC []
)

val nthStateProp = store_thm ("nthStateProp",
``(!x. P x /\ C x ==> P (f x)) ==> 
!n s.P s /\ (!m.m < n ==> C (FUNPOW f m s)) ==> P (FUNPOW f n s)``,
STRIP_TAC THEN
Induct_on `n` THEN 
SRW_TAC [] [FUNPOW] THEN
FIRST_ASSUM MATCH_MP_TAC THEN
`P (f s)`  by METIS_TAC [DECIDE ``0 < SUC n``,FUNPOW] THEN
SRW_TAC [] [] THEN
METIS_TAC [DECIDE ``m < n ==> SUC m < SUC n``,FUNPOW])


val owhileEndState = store_thm ("owhileEndState", 
``((owhile C f s = SOME s') /\ (!x.P x /\ C x ==> P (f x)) /\ P s) ==> P s'``,
SRW_TAC [] [owhile_def,owhile_EQ_SOME] THEN
numLib.LEAST_ELIM_TAC THEN SRW_TAC [][] THENL[
METIS_TAC [],
METIS_TAC [nthStateProp]]
)


(* mwhile G C can have three different results:
    NONE - went into an infinite loop
    SOME NONE - aborted (body returned NONE on some state) 
    SOME (SOME s) - successful termination in state s 
*)

val mwhile = Define`
  mwhile g f s = 
    owhile (\opt. case opt of NONE -> F || SOME s -> g s)
           (\opt. case opt of NONE -> NONE 
                           || SOME s -> f s)
           (SOME s)
`;

val mwhile_COND = store_thm(
  "mwhile_COND",
  ``mwhile g f s = 
           if g s then 
              case f s of 
                NONE -> SOME NONE
             || SOME s' -> mwhile g f s'
           else SOME (SOME s)``,
  SRW_TAC [][mwhile] THENL [
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [owhile_thm])) THEN 
    SRW_TAC [][] THEN 
    Cases_on `f s` THEN SRW_TAC [][] THEN 
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [owhile_thm])) THEN 
    SRW_TAC [][],

    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [owhile_thm])) THEN 
    SRW_TAC [][]
  ]);



(*
val mwhile_EQ_NONE = store_thm(
"mwhile_EQ_NONE",
``!C f s.(mwhile C f s = NONE) = 
~terminates ((\opt. case opt of NONE -> T || SOME x -> C x),
             (\opt. case opt of NONE -> NONE || SOME x -> f x), SOME s)``,
SRW_TAC [][mwhile, terminates_def, owhile_def] THEN 
Cases_on `FUNPOW (\opt. case opt of NONE -> NONE || SOME s -> f s) n (SOME s)` THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `n`  THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []
METIS_TAC [NEW_THEORY])
*)

(*
val mwhile_EQ_SOME = store_thm(
"mwhile_EQ_SOME", 
``(?s'.mwhile C f s = SOME s') = terminates ((\opt. case opt of NONE -> T || SOME x -> C x),
                                  (\opt. case opt of NONE -> NONE || SOME x -> f x), SOME s)``,
SRW_TAC [] [EQ_IMP_THM] THEN
 METIS_TAC [optionTheory.NOT_SOME_NONE,optionTheory.option_nchotomy,owhile_EQ_NONE,
mwhile_EQ_NONE])
*)

val mwhileEndCond = store_thm ("mwhileEndCond", 
``(mwhile C f s = SOME (SOME s')) ==> ~ C s'``,
SRW_TAC [] [mwhile] THEN
METIS_TAC [owhileEndCond, optionTheory.option_case_def]) 



val mwhileEndState = store_thm ("mwhileEndState",
``(mwhile C f s = SOME (SOME s')) /\
(!x x'. P x /\ C x /\ (f x = SOME x') ==> P x') /\
P s ==> P s'``,
SIMP_TAC (srw_ss()) [mwhile] THEN
Q.MATCH_ABBREV_TAC `(owhile CC ff (SOME s) = SOME (SOME s')) /\
(!x y. P x /\ C x /\ (f x = SOME y) ==> P y) /\
P s ==> P s'` THEN
STRIP_TAC THEN
Q.ABBREV_TAC `PP = \x. case x of NONE -> T || SOME s -> P s` THEN
`(!x. PP x /\ CC x ==> PP (ff x)) /\ PP (SOME s) ==> PP (SOME s')`
by METIS_TAC [owhileEndState] THEN
markerLib.UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x` THEN SRW_TAC [][] THEN Cases_on `f x'` THEN SRW_TAC [][] THEN
METIS_TAC []);



val mlDir = ref ("./theoryML/");

(* val _ =
 let open emitLib
 in emitML (!mlDir)
   ("whileLemmas",
    DEFN owhile_thm
    :: DEFN mwhile
    :: [])
 end;
*)

val _ = export_theory ();

