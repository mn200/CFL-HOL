(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory listTheory;
open pred_setTheory listLemmasTheory;

val _ = new_theory "regexp";

val _ = Hol_datatype `symbol = TS of string| NTS of string`;

val isTmnlSym = Define `(isTmnlSym sym = (?s.sym = (TS s)))`;

val isNonTmnlSym = Define `isNonTmnlSym sym = (?s.sym = (NTS s))`;


val isTmnlSymML = store_thm ("isTmnlSymML",
 ``(isTmnlSym (NTS nt) = F) /\ (isTmnlSym (TS ts) = T)``,
SRW_TAC [] [isTmnlSym] 
); 


val isNonTmnlSymML = store_thm ("isNonTmnlSymML",
``(isNonTmnlSym (NTS nt) = T) /\ (isNonTmnlSym (TS s) = F)``,
SRW_TAC [] [isNonTmnlSym]
)

val tmnlSym = Define `tmnlSym (TS tmnl) = tmnl`;

val nonTmnlSym = Define `nonTmnlSym (NTS ntmnl) = ntmnl`;

val nts2str = Define `nts2str (NTS s) = s`

val ts2str = Define `ts2str (TS s) = s`

val sym2Str = Define `(sym2Str (TS s) = s) /\ (sym2Str (NTS s) = s)`;


val sym_r1a = store_thm ("sym_r1a",
``isTmnlSym e ==> ~ isNonTmnlSym e``,
SRW_TAC [] [isTmnlSym,isNonTmnlSym] THEN
Cases_on `e` THEN
METIS_TAC [isTmnlSym,isNonTmnlSym] 
);


val sym_r1b = store_thm ("sym_r1b",
``~isTmnlSym e = isNonTmnlSym e``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Cases_on `e` THENL[
METIS_TAC [isTmnlSym,isNonTmnlSym],
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym,isTmnlSym]],
Cases_on `e` THENL[
FULL_SIMP_TAC (srw_ss())[isTmnlSym,isNonTmnlSym],
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym,isTmnlSym]]
]);

val sym_r2 = store_thm ("sym_r2",
``isTmnlSym e ==> ~(?n.e=NTS n)``,
SRW_TAC [] [] THEN 
Cases_on `e=NTS n` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym]
);

val sym_r3 = store_thm ("sym_r3",
``!v.EVERY isTmnlSym v ==> ~(?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM]THEN
Cases_on `n` THENL[
SRW_TAC [] [isTmnlSym, isNonTmnlSym],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym,isNonTmnlSym] THEN
METIS_TAC [isTmnlSym,isNonTmnlSym,sym_r1b,EQ_IMP_THM]]);


val sym_r3b = store_thm ("sym_r3b",
``!v.EVERY isNonTmnlSym v ==> ~(?n s1 s2.(v=s1++[n]++s2) /\ isTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM]THEN
Cases_on `n` THENL[
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym,isNonTmnlSym] THEN
METIS_TAC [isTmnlSym,isNonTmnlSym,sym_r1b,EQ_IMP_THM],
SRW_TAC [] [isTmnlSym, isNonTmnlSym]
]);


val sym_r4 = store_thm ("sym_r4",
``!v.EVERY isTmnlSym v ==> ~(?n. MEM n v /\ ~isTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
Cases_on `n` THEN
METIS_TAC [isTmnlSym,isNonTmnlSym,MEM]
);


val sym_r4b = store_thm ("sym_r4b",
``!v.~EVERY isTmnlSym v ==> (?n. MEM n v /\ isNonTmnlSym n)``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,EXISTS_MEM] THEN
METIS_TAC [isTmnlSym,isNonTmnlSym,MEM,sym_r1b]
);


val sym_r5 = store_thm ("sym_r5",
``!v.~(?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n) ==> EVERY isTmnlSym v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
SRW_TAC [] [] THEN
Cases_on `e` THENL[
SRW_TAC [] [isTmnlSym, isNonTmnlSym],
SRW_TAC [] [isTmnlSym, isNonTmnlSym] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
METIS_TAC [isNonTmnlSym,isTmnlSym]]);

val sym_r6 = store_thm ("sym_r6",
``!v.EVERY isTmnlSym v = (~(?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n))``,
SRW_TAC [] [EQ_IMP_THM] THENL[
METIS_TAC [sym_r3], METIS_TAC [sym_r5]
]
);

val sym_r7 = store_thm ("sym_r7",
``!v.~(EVERY isTmnlSym v) ==> ?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,rgr_r9eq,sym_r1b] THEN
MAP_EVERY Q.EXISTS_TAC [`e`,`r1`,`r2`] THEN
SRW_TAC [] []
);


val sym_r7b = store_thm ("sym_r7b",
``!v.~(EVERY isNonTmnlSym v) ==> ?n s1 s2.(v=s1++[n]++s2) /\ isTmnlSym n``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,rgr_r9eq,sym_r1b] THEN
MAP_EVERY Q.EXISTS_TAC [`e`,`r1`,`r2`] THEN
METIS_TAC [sym_r1b]
);


val rightnt = store_thm ("rightnt",
``!s.~EVERY isTmnlSym s ==> 
?l1 n l2. (s= l1++[NTS n]++l2) /\ EVERY isTmnlSym l2``,
Induct_on `s` THEN SRW_TAC [] [] THENL[
Cases_on `EVERY isTmnlSym s` THENL[
Cases_on `h` THEN METIS_TAC [isTmnlSym, APPEND],
METIS_TAC [APPEND]],
`~ EVERY isTmnlSym s` by SRW_TAC [] [] THEN METIS_TAC [APPEND]])


(* Regular Expressions *)

(* Definition of a regexp *)

val _ = Hol_datatype `rexp =    EmptyLang   | Atom of symbol   | Union of rexp => rexp   | Conc of rexp => rexp   | Star of rexp`;


(* Concatenation *)
(* conc :: a list set => a list set => a list set 
val conc = Define `(conc [] (b::bs) = (b::bs)) /\ (conc (a::as) (b::bs) = (MAP (STRCAT a) (b::bs)) ++ (conc as (b::bs)))`;
*)

val conc = Define `conc as bs = {s | ?u v. u IN as /\ v IN bs /\ (s = u ++ v)}`;

(* Union *)
val union = Define `union as bs = {s | s IN as \/ s IN bs}`;

(* 
Star
(defined inductively)

star :: a list set => a list set
[] <- star A
a <- A and as <- star A => a++as <- star A
*)


val starn = Define `(starn l 0 = {[]})  /\ (starn l n = {s | ?u v. u IN l /\ v IN (starn l (n-1)) /\ (s =  u ++ v)})`;
(* Define A* + prove alternate defn of * *)

val (star_rules, star_ind, star_cases) = Hol_reln`  (star A []) /\   (!s. s IN A ==> star A s) /\  (!s1 s2. s1 IN A /\ s2 IN A ==> star A (s1 ++ s2))`;

(* Language denoted by a rexp *)
(* lang :: a rexp => a list set *)
(* Includes nonterms as well *)
val lang = Define `(lang EmptyLang = {}) /\ (lang (Atom tmnl) = {[sym2Str tmnl]}) /\ (lang (Union r s) = lang r UNION lang s) /\ (lang (Conc r s) = conc (lang r) (lang s)) /\ (lang (Star r) = star (lang r))`;

val mlDir = ref ("./theoryML/");

val _ =
 let open EmitML
 in emitML (!mlDir)
   ("regexp",
OPEN ["num"]
    :: MLSIG "type num = numML.num"
    :: DATATYPE `symbol = TS of string| NTS of string`
    :: DEFN tmnlSym
    :: DEFN nonTmnlSym
    :: DEFN isTmnlSymML
    :: DEFN isNonTmnlSymML
    :: DEFN sym2Str
    :: [])
 end;

val _ = export_theory ();

