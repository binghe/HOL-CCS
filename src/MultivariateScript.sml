(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Multivariate CCS Theory and Unique Solution of Equations   *)
(*                                                                            *)
(* AUTHOR        : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib listTheory alistTheory finite_mapTheory;

(* unused for now:
 pairTheory prim_recTheory arithmeticTheory combinTheory;
 *)

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory
     ObsCongrTheory ContractionTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory;

(* unused for now:
open StrongEQLib StrongLawsTheory WeakEQLib WeakLawsTheory;
open ObsCongrLib ObsCongrLawsTheory TraceTheory ExpansionTheory;
 *)

val _ = new_theory "Multivariate";

val set_ss = std_ss ++ PRED_SET_ss;

(*                           -- DESIGN NOTES --

1. What's a multivariate CCS equation?

   - Xs: A list of equation variables: [X1; X2; ...; Xn] :'a list
   - Es: A list of arbitrary CCS terms: [E1; E2; ...; En] :('a,'b) CCS list

   ``ALL_DISTINCT Xs /\ (LENGTH Xs = LENGTH Es)`` must hold.

   The multivariete equation is actually the following equation group:

    / var (EL 0 Xs) = (EL 0 Es)
    | var (EL 1 Xs) = (EL 1 Es)
    + var (EL 2 Xs) = (EL 2 Es)   or   `MAP var Xs = Es`
    |              ...
    \ var (EL n Xs) = (EL n Es)

   The `=` (at left) could be `STRONG_EQUIV`, `WEAK_EQUIV`, `OBS_CONGR`
   or even `contracts`. (In the last case it's actually an inequation group.)

   Note that, it does NOT matter each `(EL i Es)` contains what variables:
   those free variables outside of X simply lead to no transition
   (like nil) according to [VAR_NO_TRANS]; those in X but not in `(EL i n)`
   simply causes `(EL i n)` not changed after the substitution.

   Also, we never need to express such this equation (group) in any
   theorem. Instead, we only need to express their solution(s).

2. What's a solution of (above) multiviriate CCS equation (group)?

   - Ps: A list of arbitrary CCS terms: [P1; P2; ...; Pn] :('a,'b) CCS list

   `Ps` is a solution of (above) multivariate CCS equation (group) iff:

    / (EL 0 Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)
    | (EL 1 Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)
    + (EL 2 Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)
    |          ...
    \ (EL n Ps) = SUBST (ZIP (Xs, Ps)) (EL 0 Es)

   or

    Ps = MAP (SUBST (ZIP Xs Ps)) Es

   (where ``ZIP Xs Ps`` is an alist of type ``:('a # ('a,'b) CCS) list``)

   or (abbrev.)

    (CCS_solution Es Xs Ps) : bool

   and

    (CCS_solution Es Xs) is the set of all solutions of `MAP var Xs = Es`.

3. What's an unique solution of (above) multivariate CCS equation (group)?

   If Ps and Qs are both solutions of `MAP var Xs = Es`, i.e.

      `CCS_solution Ps $= Es Xs /\ CCS_solution Qs $= Es Xs`,

   then, beside ``Ps = Qs`, we may also have:

      `(LIST_REL STRONG_EQUIV) Ps Qs`, or
      `(LIST_REL WEAK_EQUIV) Ps Qs`, or
      `(LIST_REL OBS_EQUIV) Ps Qs`

   Ps (or Qs) is called an "unique" solution (up to the corresponding
   equivalence relation).

4. What's a "weakly guarded" multivariate CCS equation (group)?

   An equation group is weakly guarded iff so is each equation in it.

  `weakly_guarded Xs E` means, for each X in Xs, if X is replaced by a
   hole [], the resulting context as lambda-term (\t. CCS_Subst E t X)
   must be WG:

   weakly_guarded Es Xs =
     !E X. MEM E Es /\ MEM X Xs ==> WG (\t. CCS_Subst E t X)

   NOTE 1: using `!e. CONTEXT e /\ (e (var X) = E) ==> WG e` is wrong.
   It appears in the conclusion of our EXPRESS/SOS'18 paper. The problem
   is, it's possible that there's no such CONTEXT e at all, e.g.
   when equation variables appear inside recursion operators, then
   `E` is still identified as a weakly guarded equation.

   Currently, there's a limitation that, our definition of WG
   doesn't have any recursion operator (unless in an irrelevant `p` of
   `\t. p`). This means, our equation (free) variables can never be
   wrapped by another bounded variable in the CCS equations.  Fixing
   this limitation may falsify the entire unique-solution of
   contraction theorm as I currently observed (but didn't say anywhere
   else), simply because certain proof steps cannot be fixed under
   this possibility. This is a potential TODO direction in the future.

   NOTE 2: using `?e. CONTEXT e /\ (e (var X) = E) /\ WG e` is even
   worse, because `E` may contain multiple `var X` as free variables,
   thus it's possible that there exists two different CONTEXTs, say
   `e1` and `e2`, such that

     e1 <> e2 /\ (e1 (var X) = e2 (var X) = E) /\ WG e1 /\ WG e2

   but none of them are really weakly guarded for all appearences of
   (var X) in E.

   NOTE 3: the "weak guardedness" of Es is always connected with Xs,
   as we don't need to care about those (free) variables in Es that
   are outside of Xs. Even they're not weakly guarded, we don't care,
   as they will be never substituted as an equation variable, instead
   they just function like a nil (with no further transition).  In
   this way, we eliminated the needs of using possibly-wrong
   definition of FV (the set/list of free variables), as the same
   variable may appear both free and bounded in different sub-term of
   the same CCS term.

   -- Chun Tian, Aug 10, 2019 (Giardino di via Fermi, Trento, Italy)
*)

(* The use of finite_mapTheory to get rid of substitution orders was
   suggested by Konrad Slind (HOL mailing list on Oct 23, 2017):

  "There are all kinds of issues with substitutions and applying them
   to term-like structures. I would probably start by choosing finite
   maps (finite_mapTheory) as the representation for variable
   substitutions since they get rid of most if not all the issues
   with ordering of replacements. The alistTheory provides a more
   computationally friendly version, and provides a formal connection
   back to fmaps.

   Also see <holdir>/examples/unification/triangular/first-order
   for a unification case study."
 *)
Definition CCS_SUBST_def :
   (CCS_SUBST (fm :'a |-> ('a, 'b) CCS) nil = nil) /\
   (CCS_SUBST fm (prefix u E) = prefix u (CCS_SUBST fm E)) /\
   (CCS_SUBST fm (sum E1 E2)  = sum (CCS_SUBST fm E1)
                                    (CCS_SUBST fm E2)) /\
   (CCS_SUBST fm (par E1 E2)  = par (CCS_SUBST fm E1)
                                    (CCS_SUBST fm E2)) /\
   (CCS_SUBST fm (restr L E)  = restr L (CCS_SUBST fm E)) /\
   (CCS_SUBST fm (relab E rf) = relab (CCS_SUBST fm E) rf) /\
   (CCS_SUBST fm (var X)      = var X) /\
   (CCS_SUBST fm (rec X E)    = (rec X (CCS_SUBST fm E))) /\
   (CCS_SUBST fm (Var X)      = if X IN FDOM fm then fm ' X else (Var X))
End

(* The order of arguments is swapped: `CCS_Subst E fm` *)
val _ = overload_on ("CCS_Subst", ``\E fm. CCS_SUBST fm E``);

(* From a key list and a value list (of same length) to a finite map *)
Definition fromList_def :
    fromList Xs Ps = alist_to_fmap (ZIP (Xs,Ps))
End

val _ = overload_on ("|->", ``fromList``);
val _ = set_fixity "|->" (Infix(NONASSOC, 100));

Theorem IN_fromList :
    !X Xs Ps. (LENGTH Ps = LENGTH Xs) ==>
              (X IN FDOM (fromList Xs Ps) <=> MEM X Xs)
Proof
    RW_TAC std_ss [fromList_def, FDOM_alist_to_fmap, MAP_ZIP]
QED

(* ('a, 'b) CCS -> 'a set (set of free variables) *)
Definition FV_def :
   (FV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (FV (prefix u p)        = FV p) /\
   (FV (sum p q)           = (FV p) UNION (FV q)) /\
   (FV (par p q)           = (FV p) UNION (FV q)) /\
   (FV (restr L p)         = FV p) /\
   (FV (relab p rf)        = FV p) /\
   (FV (var X)             = EMPTY) /\
   (FV (rec X p)           = FV p) /\
   (FV (Var X)             = {X})
End

val IS_PROC_def = Define `
    IS_PROC E <=> (FV E = EMPTY)`;

val ALL_PROC_def = Define `
    ALL_PROC Es <=> EVERY IS_PROC Es`;

(* KEY result: if Xs is disjoint with free variables of E, then E{_/Xs} = E *)
Theorem CCS_SUBST_NOT_FV :
    !Xs E. DISJOINT (FV E) (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==> (CCS_Subst E (Xs |-> Ps) = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [Once CCS_SUBST_def, FV_def, Once fromList_def,
                   FDOM_alist_to_fmap, MAP_ZIP]
QED

(* ================================================================= *)
(*   Weakly guarded equations                                        *)
(* ================================================================= *)

Definition weakly_guarded_def :
    weakly_guarded Xs =
     \E. EVERY (\X. WG (\t. CCS_SUBST (FEMPTY |+ (X,t)) E)) Xs
End

Theorem EVERY_weakly_guarded :
    !Xs Es. EVERY (weakly_guarded Xs) Es ==>
        !E X. MEM E Es /\ MEM X Xs ==>
            WG (\t. CCS_SUBST (FEMPTY |+ (X,t)) E)
Proof
    SRW_TAC[] [weakly_guarded_def, EVERY_MEM]
QED

Theorem weakly_guarded_sum :
    !Xs E1 E2. weakly_guarded Xs (sum E1 E2) ==>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    SRW_TAC [] [weakly_guarded_def, EVERY_MEM] (* 2 goals, same tactics *)
 >> RES_TAC >> fs [CCS_SUBST_def]
 >> METIS_TAC [WG4_backward]
QED

Theorem weakly_guarded_par :
    !Xs E1 E2. weakly_guarded Xs (par E1 E2) ==>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    SRW_TAC [] [weakly_guarded_def, EVERY_MEM] (* 2 goals, same tactics *)
 >> RES_TAC >> fs [CCS_SUBST_def]
 >> METIS_TAC [WG5_backward]
QED

Theorem weakly_guarded_restr :
    !Xs L E. weakly_guarded Xs (restr L E) ==> weakly_guarded Xs E
Proof
    SRW_TAC [] [weakly_guarded_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_SUBST_def]
 >> METIS_TAC [WG6_backward]
QED

Theorem weakly_guarded_relab :
    !Xs E rf. weakly_guarded Xs (relab E rf) ==> weakly_guarded Xs E
Proof
    SRW_TAC [] [weakly_guarded_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_SUBST_def]
 >> METIS_TAC [WG7_backward]
QED

(* KEY result: if E[t/X] = E[t'/X] for all t t', X must not be free in E *)
val CCS_SUBST_EQ_IMP = Q.prove (
   `!X E. (!E1 E2. CCS_SUBST (FEMPTY |+ (X,E1)) E =
                   CCS_SUBST (FEMPTY |+ (X,E2)) E) ==> X NOTIN (FV E)`,
    Suff `!X E. X IN (FV E) ==>
                ?E1 E2. CCS_SUBST (FEMPTY |+ (X,E1)) E <>
                        CCS_SUBST (FEMPTY |+ (X,E2)) E` >- METIS_TAC []
 >> GEN_TAC >> Induct_on `E` (* 9 subgoals *)
 >> SRW_TAC [] [CCS_SUBST_def, FV_def] (* 5 subgoals left *)
 >| [ RES_TAC >> take [`E1`, `E2`] >> DISJ1_TAC >> art [],
      RES_TAC >> take [`E1`, `E2`] >> DISJ2_TAC >> art [],
      RES_TAC >> take [`E1`, `E2`] >> DISJ1_TAC >> art [],
      RES_TAC >> take [`E1`, `E2`] >> DISJ2_TAC >> art [],
      Q.EXISTS_TAC `nil` >> METIS_TAC [CCS_distinct_exists] ]);

(* KEY result, c.f. WG8_IMP_CONST *)
Theorem weakly_guarded_rec :
    !Xs Y E. weakly_guarded Xs (rec Y E) ==> DISJOINT (FV E) (set Xs)
Proof
    SRW_TAC [] [weakly_guarded_def, EVERY_MEM]
 >> CCONTR_TAC >> fs [IN_DISJOINT]
 >> RES_TAC
 >> fs [CCS_SUBST_def]
 >> Q.ABBREV_TAC `e = \t. CCS_SUBST (FEMPTY |+ (x,t)) E`
 >> Know `WG (\t. rec Y (e t))` >- (Q.UNABBREV_TAC `e` >> fs [])
 >> Q.PAT_X_ASSUM `WG (\t. P)` K_TAC (* clean up *)
 >> DISCH_TAC
 >> IMP_RES_TAC WG8_IMP_CONST
 >> Q.UNABBREV_TAC `e` >> fs [CCS_const_def]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP CCS_SUBST_EQ_IMP))
QED

(*
Theorem TRANS_FV :
    !E u E'. TRANS E u E' ==> FV E' SUBSET FV E
Proof
    HO_MATCH_MP_TAC TRANS_ind
 >> RW_TAC set_ss [FV_def]

 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Reverse (Cases_on `X IN FV E`)
 >- (`FV E DELETE X = FV E` by PROVE_TAC [GSYM DELETE_NON_ELEMENT] \\
     fs [CCS_Subst_NOT_FV])
 >> `FV E = {X}` by PROVE_TAC [DELETE_EQ_SING]
 >> POP_ASSUM MP_TAC >> KILL_TAC
 (* FV E = {X} ==> FV (CCS_Subst E (rec X E) X) = {} *)
 >> Suff `FV (CCS_Subst E (rec X E) X) <> EMPTY ==> FV E <> {X}`
 >- METIS_TAC []
 >> RW_TAC std_ss [GSYM MEMBER_NOT_EMPTY]
 >> cheat
QED
 *)

(* ================================================================= *)
(*   Unique Solution of Equations                                    *)
(* ================================================================= *)

val _ = overload_on ( "STRONG_EQUIV", ``LIST_REL  STRONG_EQUIV``);
val _ = overload_on (   "WEAK_EQUIV", ``LIST_REL    WEAK_EQUIV``);
val _ = overload_on (    "OBS_CONGR", ``LIST_REL     OBS_CONGR``);
val _ = overload_on ("OBS_contracts", ``LIST_REL OBS_contracts``);

(* Lemma 4.13 in Milner's book [1] (the full version):

   If the variable X is weakly guarded in E, and E{Ps/Xs} --u-> P',
   then P' takes the form E'{Ps/Xs} (for some expression E'), and
   moreover, for any Qs, E{Qs/Xs} --u-> E'{Qs/Xs}.

   Additional requirements in the multivariate case (HOL):
   - E contains free variables up to Xs
 *)
Theorem strong_unique_solution_lemma : (* full version *)
    !Xs E. weakly_guarded Xs E /\ (FV E) SUBSET (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==>
                !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
                       ?E'. (P' = CCS_SUBST (fromList Xs Ps) E') /\
                            !Qs. (LENGTH Qs = LENGTH Xs) ==>
                                 TRANS (CCS_SUBST (fromList Xs Qs) E) u
                                       (CCS_SUBST (fromList Xs Qs) E')
Proof
    GEN_TAC >> Induct_on `E` >> rpt STRIP_TAC (* 9 subgoals *)
 (* Case 0: E = nil, impossible *)
 >- fs [CCS_SUBST_def, NIL_NO_TRANS]
 (* Case 1: E = var Y (recursion variable), still impossible *)
 >- fs [CCS_SUBST_def, VAR_NO_TRANS]
 (* Case 2: E = b.E' *)
 >- (rename1 `weakly_guarded Xs (prefix b E)` \\
     fs [CCS_SUBST_def, TRANS_PREFIX_EQ] \\
     Q.EXISTS_TAC `E` >> REWRITE_TAC [])
 (* Case 3: E = E1 + E2 *)
 >- (IMP_RES_TAC weakly_guarded_sum \\
     fs [CCS_SUBST_def, TRANS_SUM_EQ, FV_def] \\ (* 2 subgoals, same tactics *)
     RES_TAC >> fs [] >> Q.EXISTS_TAC `E''` >> fs [])
 (* Case 4: E = E1 || E2 *)
 >- (rename1 `weakly_guarded Xs (E1 || E2)` \\
     IMP_RES_TAC weakly_guarded_par \\
     fs [CCS_SUBST_def, TRANS_PAR_EQ, FV_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         K_TAC \\
       RW_TAC std_ss [] \\
       RES_TAC >> Q.EXISTS_TAC `E' || E2` \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_Subst E' (fromList Xs Qs)` >> REWRITE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         K_TAC \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       RES_TAC >> Q.EXISTS_TAC `E1 || E''` \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ2_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_Subst E'' (fromList Xs Qs)` >> REWRITE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       RES_TAC >> Q.EXISTS_TAC `E' || E''` \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
       GEN_TAC >> DISCH_TAC >> NTAC 2 DISJ2_TAC \\
       take [`CCS_Subst E' (fromList Xs Qs)`,
             `CCS_Subst E'' (fromList Xs Qs)`, `l`] >> fs [] ])
 (* Case 5: E = restr f E' *)
 >- (IMP_RES_TAC weakly_guarded_restr \\
     fs [CCS_SUBST_def, TRANS_RESTR_EQ, FV_def] \\ (* 2 subgoals, same tactics *)
     RES_TAC >> Q.EXISTS_TAC `restr f E'` \\
     rfs [CCS_SUBST_def])
 (* Case 6: E = relab E' R *)
 >- (IMP_RES_TAC weakly_guarded_relab \\
     fs [CCS_SUBST_def, TRANS_RELAB_EQ, FV_def] \\
     Q.PAT_X_ASSUM
       `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==> _`
       (MP_TAC o (Q.SPEC `Ps`)) \\
     RW_TAC std_ss [] \\
     RES_TAC >> Q.EXISTS_TAC `relab E' R` \\
     ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
     GEN_TAC >> DISCH_TAC \\
     take [`u'`, `CCS_Subst E' (fromList Xs Qs)`] >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* Case 7: E = rec Y E' *)
 >- (FULL_SIMP_TAC (srw_ss()) [CCS_SUBST_def, FV_def] \\
     cheat)
 (* Case 8: E = Var a (equation variable, impossible) *)
 >> fs [weakly_guarded_def, EVERY_MEM, CCS_SUBST_def, FV_def]
 >> RES_TAC >> fs [NO_WG0]
QED

(* NOTE: Es MUST contain free variables up to Xs *)
Definition CCS_equation_def :
    CCS_equation (Xs :'a list) (Es :('a, 'b) CCS list) <=>
        ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs) /\
        EVERY (\E. (FV E) SUBSET (set Xs)) Es
End

(* A solution Ps of the CCS equation (group) Es[Xs] up to R *)
Definition CCS_solution_def :
    CCS_solution (Ps :('a, 'b) CCS list) R Es Xs <=>
        ALL_PROC Ps /\
        LIST_REL R Ps (MAP (CCS_SUBST (fromList Xs Ps)) Es)
End

(* THE STAGE THEOREM *)
Theorem strong_unique_solution :
    !Es Xs. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. CCS_solution Ps STRONG_EQUIV Es Xs /\
                CCS_solution Qs STRONG_EQUIV Es Xs ==>
                LIST_REL STRONG_EQUIV Ps Qs
Proof
    cheat
QED

(* THE FINAL THEOREM *)
Theorem unique_solution_of_rooted_contractions :
    !Es Xs. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. CCS_solution Ps OBS_contracts Es Xs /\
                CCS_solution Qs OBS_contracts Es Xs ==>
                LIST_REL OBS_CONGR Ps Qs
Proof
    cheat
QED

val _ = export_theory ();
val _ = html_theory "Multivariate";
