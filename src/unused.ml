(**********************************************************************)
(*  Free and bounded variables of CCS expressions (old, disabled)     *)
(**********************************************************************)

(*
(* ('a, 'b) CCS -> 'a set (set of bound variables) *)
Definition BV_def :
   (BV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (BV (prefix u p)        = BV p) /\
   (BV (sum p q)           = (BV p) UNION (BV q)) /\
   (BV (par p q)           = (BV p) UNION (BV q)) /\
   (BV (restr L p)         = BV p) /\
   (BV (relab p rf)        = BV p) /\
   (BV (var X)             = EMPTY) /\
   (BV (rec X p)           = X INSERT (BV p))
End

(* ('a, 'b) CCS -> 'a set (set of free variables) *)
Definition FV_def :
   (FV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (FV (prefix u p)        = FV p) /\
   (FV (sum p q)           = (FV p) UNION (FV q)) /\
   (FV (par p q)           = (FV p) UNION (FV q)) /\
   (FV (restr L p)         = FV p) /\
   (FV (relab p rf)        = FV p) /\
   (FV (var X)             = {X}) /\
   (FV (rec X p)           = (FV p) DELETE X)
End

(* however it doesn't lead to TRANS_PROC *)
Theorem FV_SUBSET :
    !X E E'. FV (CCS_Subst E E' X) SUBSET (FV E) UNION (FV E')
Proof
    GEN_TAC
 >> Induct_on `E` >> RW_TAC set_ss [FV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

val IS_PROC_def = Define `
    IS_PROC E <=> (FV E = EMPTY)`;

val ALL_PROC_def = Define `
    ALL_PROC Es <=> EVERY IS_PROC Es`;

Theorem TRANS_PROC :
    !E u E'. TRANS E u E' ==> IS_PROC E ==> IS_PROC E'
Proof
    HO_MATCH_MP_TAC TRANS_ind
 >> RW_TAC set_ss [FV_def, IS_PROC_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 (* FV E = ∅ ⇒ FV (CCS_Subst E (rec X E) X) = ∅ *)
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] FV_SUBSET)
fs [FV_def]
ASM_SET_TAC []
 >> ASM_SET_TAC [FV_def]
QED

Theorem BV_REC :
    !X E. X IN BV (rec X E)
Proof
    RW_TAC std_ss [BV_def, IN_INSERT]
QED

Theorem BV_SUBSET :
    !X E E'. (BV E) SUBSET (BV (rec X E)) /\
             (BV E) SUBSET (BV (sum E E')) /\ (BV E') SUBSET (BV (sum E E')) /\
             (BV E) SUBSET (BV (par E E')) /\ (BV E') SUBSET (BV (par E E'))
Proof
    rpt GEN_TAC >> SET_TAC [BV_def]
QED

val lemma1 = Q.prove (
   `!X E. X NOTIN (FV E) ==> !E'. (CCS_Subst E E' X = E)`,
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* one left *)
 >> Cases_on `a = X` >- fs []
 >> RES_TAC >> ASM_SIMP_TAC std_ss []);

val lemma2 = Q.prove (
   `!X E. (!E'. CCS_Subst E E' X = E) ==> X NOTIN (FV E)`,
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 2 goals left *)
 >- (CCONTR_TAC >> fs [] \\
     PROVE_TAC [Q.SPEC `var a` CCS_distinct_exists])
 >> Cases_on `X = a` >- fs []
 >> DISJ1_TAC >> fs []);

(* KEY result: X is not a free variable of E if and only if E{E'/X} = E *)
Theorem CCS_Subst_NOT_FV :
    !X E. X NOTIN (FV E) <=> !E'. (CCS_Subst E E' X = E)
Proof
    METIS_TAC [lemma1, lemma2]
QED

(* KEY result: if E[t/X] = E[t'/X] for all t t', X must not be free in E *)
Theorem CCS_Subst_EQ_IMP :
    !X E. (!E1 E2. CCS_Subst E E1 X = CCS_Subst E E2 X) ==> X NOTIN (FV E)
Proof
    Suff `!X E. X IN (FV E) ==> ?E1 E2. CCS_Subst E E1 X <> CCS_Subst E E2 X`
 >- METIS_TAC []
 >> GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 5 subgoals left *)
 >- (Q.EXISTS_TAC `nil` >> METIS_TAC [CCS_distinct_exists])
 >| [ RES_TAC >> take [`E1`, `E2`] >> DISJ1_TAC >> art [],
      RES_TAC >> take [`E1`, `E2`] >> DISJ2_TAC >> art [],
      RES_TAC >> take [`E1`, `E2`] >> DISJ1_TAC >> art [],
      RES_TAC >> take [`E1`, `E2`] >> DISJ2_TAC >> art [] ]
QED

Theorem FV_PREFIX :
    !X E u E'. FV (CCS_Subst E (rec X (prefix u E')) X) =
               FV (CCS_Subst E (rec X E') X)
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def]
QED

Theorem FV_SUM :
    !X E E1 E2. FV (CCS_Subst E (rec X (E1 + E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 4 subgoals *)
 >> SET_TAC []
QED

Theorem FV_PAR :
    !X E E1 E2. FV (CCS_Subst E (rec X (E1 || E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC set_ss [CCS_Subst_def, FV_def] (* 4 subgoals *)
 >> SET_TAC []
QED

(**********************************************************************)
(* Free and bounded variables ('a)                                    *)
(**********************************************************************)

Definition DELETE_ELEMENT_def :
   (DELETE_ELEMENT e [] = []) /\
   (DELETE_ELEMENT e (x :: l) =
       if (e = x) then DELETE_ELEMENT e l else x :: DELETE_ELEMENT e l)
End

val NOT_IN_DELETE_ELEMENT = store_thm (
   "NOT_IN_DELETE_ELEMENT",
  ``!e L. ~MEM e (DELETE_ELEMENT e L)``,
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT_def, MEM]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT_def]
 >> Cases_on `e = h` >> fs []);

val DELETE_ELEMENT_FILTER = store_thm (
   "DELETE_ELEMENT_FILTER",
  ``!e L. DELETE_ELEMENT e L = FILTER ((<>) e) L``,
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT_def, FILTER]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT_def, FILTER]
 >> Cases_on `e = h` >> fs []);

val LENGTH_DELETE_ELEMENT_LEQ = store_thm (
   "LENGTH_DELETE_ELEMENT_LEQ",
  ``!e L. LENGTH (DELETE_ELEMENT e L) <= LENGTH L``,
    rpt GEN_TAC
 >> REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> MP_TAC (Q.SPECL [`\y. e <> y`, `\y. T`] LENGTH_FILTER_LEQ_MONO)
 >> BETA_TAC >> simp []);

val LENGTH_DELETE_ELEMENT_LE = store_thm (
   "LENGTH_DELETE_ELEMENT_LE",
  ``!e L. MEM e L ==> LENGTH (DELETE_ELEMENT e L) < LENGTH L``,
    rpt GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [MEM]
 >> GEN_TAC >> REWRITE_TAC [MEM, DELETE_ELEMENT_def]
 >> Cases_on `e = h` >> fs []
 >> MP_TAC (Q.SPECL [`h`, `L`] LENGTH_DELETE_ELEMENT_LEQ)
 >> KILL_TAC >> RW_TAC arith_ss []);

val EVERY_DELETE_ELEMENT = store_thm (
   "EVERY_DELETE_ELEMENT",
  ``!e L P. P e /\ EVERY P (DELETE_ELEMENT e L) ==> EVERY P L``,
    GEN_TAC >> Induct_on `L`
 >- RW_TAC std_ss [DELETE_ELEMENT_def]
 >> rpt GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT_def]
 >> Cases_on `e = h` >> fs []);

val DELETE_ELEMENT_APPEND = store_thm (
   "DELETE_ELEMENT_APPEND",
  ``!a L L'. DELETE_ELEMENT a (L ++ L') = DELETE_ELEMENT a L ++ DELETE_ELEMENT a L'``,
    REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> REWRITE_TAC [GSYM FILTER_APPEND_DISTRIB]);

(* not used so far, learnt from Robert Beers *)
val ALL_IDENTICAL_def = Define `
    ALL_IDENTICAL t = ?x. !y. MEM y t ==> (y = x)`;

(* (FN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val FN_definition = `
   (FN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (FN (prefix (label l) p) J = l INSERT (FN p J)) /\   (* here! *)
   (FN (prefix tau p) J       = FN p J) /\
   (FN (sum p q) J            = (FN p J) UNION (FN q J)) /\
   (FN (par p q) J            = (FN p J) UNION (FN q J)) /\
   (FN (restr L p) J          = (FN p J) DIFF (L UNION (IMAGE COMPL_LAB L))) /\
   (FN (relab p rf) J         = IMAGE (REP_Relabeling rf) (FN p J)) /\ (* here *)
   (FN (var X) J              = EMPTY) /\
   (FN (rec X p) J            = if (MEM X J) then
                                    FN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
                                else EMPTY)`;

(* (BN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val BN_definition = `
   (BN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (BN (prefix u p) J         = BN p J) /\
   (BN (sum p q) J            = (BN p J) UNION (BN q J)) /\
   (BN (par p q) J            = (BN p J) UNION (BN q J)) /\
   (BN (restr L p) J          = (BN p J) UNION L) /\ (* here *)
   (BN (relab p rf) J         = BN p J) /\
   (BN (var X) J              = EMPTY) /\
   (BN (rec X p) J            = if (MEM X J) then
                                    BN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
                                else EMPTY)`;

(* This is how we get the correct tactics (FN_tac):
 - val FN_defn = Hol_defn "FN" FN_definition;
 - Defn.tgoal FN_defn;
 *)
local
  val tactic = (* the use of `($< LEX $<)` is learnt from Ramana Kumar *)
      WF_REL_TAC `inv_image ($< LEX $<)
                            (\x. (LENGTH (SND x), ^CCS_size_tm (\x. 0) (\x. 0) (FST x)))`
   >> rpt STRIP_TAC >- (IMP_RES_TAC LENGTH_DELETE_ELEMENT_LE >> art [])
   >> REWRITE_TAC [CCS_size_def]
   >> simp [];
in
  val FN_def = TotalDefn.tDefine "FN" FN_definition tactic;
  val BN_def = TotalDefn.tDefine "BN" BN_definition tactic;
end;

(* (free_names :('a, 'b) CCS -> 'b Label set) collects all visible labels in the prefix *)
val free_names_def = Define ` (* also called "sorts" by Robin Milner *)
    free_names p = FN p (SET_TO_LIST (BV p))`;

(* (bound_names :('a, 'b) CCS -> 'b Label set) collects all visible labels in the restr *)
val bound_names_def = Define `
    bound_names p = BN p (SET_TO_LIST (BV p))`;

val FN_UNIV1 = store_thm ("FN_UNIV1",
  ``!p. free_names p <> (UNIV :'b Label set) ==> ?a. a NOTIN free_names p``,
    PROVE_TAC [EQ_UNIV]);

val FN_UNIV2 = store_thm ("FN_UNIV2",
  ``!p q. free_names p UNION free_names q <> (UNIV :'b Label set) ==>
          ?a. a NOTIN free_names p /\ a NOTIN free_names q``,
    PROVE_TAC [EQ_UNIV, IN_UNION]);
*)

