(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Unique Solution of Equations (Multivariate version)        *)
(*                                                                            *)
(* COPYRIGHT     : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory pred_setTheory pred_setLib listTheory alistTheory;

(* unused for now:
 pairTheory prim_recTheory arithmeticTheory combinTheory;
 *)

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory
     ObsCongrTheory ContractionTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory;

(* unused for now:
open StrongEQLib WeakEQLib WeakLawsTheory;
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
   definition of EV (the set of equation variables), as the same
   variable may appear both free and bounded in different sub-term of
   the same CCS term.

   -- Chun Tian, Aug 10, 2019 (Giardino di via Fermi, Trento, Italy)
*)

(* The use of alistTheory to get rid of substitution orders was
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

Definition CCS_SUBST_def :
   (CCS_SUBST (map :('a, ('a, 'b) CCS) alist) nil = nil) /\
   (CCS_SUBST map (prefix u E) = prefix u (CCS_SUBST map E)) /\
   (CCS_SUBST map (sum E1 E2)  = sum (CCS_SUBST map E1)
                                    (CCS_SUBST map E2)) /\
   (CCS_SUBST map (par E1 E2)  = par (CCS_SUBST map E1)
                                    (CCS_SUBST map E2)) /\
   (CCS_SUBST map (restr L E)  = restr L (CCS_SUBST map E)) /\
   (CCS_SUBST map (relab E rf) = relab (CCS_SUBST map E) rf) /\
   (CCS_SUBST map (var X)      = var X) /\
   (CCS_SUBST map (rec X E)    = (rec X (CCS_SUBST map E))) /\
   (CCS_SUBST map (Var X)      = if MEM X (MAP FST map)
                                 then THE (ALOOKUP map X) else (Var X))
End
*)

Definition CCS_SUBST_def :
   (CCS_SUBST (map :('a, ('a, 'b) CCS) alist) nil = nil) /\
   (CCS_SUBST map (prefix u E) = prefix u (CCS_SUBST map E)) /\
   (CCS_SUBST map (sum E1 E2)  = sum (CCS_SUBST map E1)
                                    (CCS_SUBST map E2)) /\
   (CCS_SUBST map (par E1 E2)  = par (CCS_SUBST map E1)
                                    (CCS_SUBST map E2)) /\
   (CCS_SUBST map (restr L E)  = restr L (CCS_SUBST map E)) /\
   (CCS_SUBST map (relab E rf) = relab (CCS_SUBST map E) rf) /\
   (CCS_SUBST map (var X)      = if MEM X (MAP FST map)
                                then THE (ALOOKUP map X) else (var X)) /\
   (CCS_SUBST map (rec X E)    = if MEM X (MAP FST map) then (rec X E)
                                else (rec X (CCS_SUBST map E)))
End

(* The order of arguments is swapped: `CCS_Subst E map` *)
val _ = overload_on ("CCS_Subst", ``\E map. CCS_SUBST map E``);

(* From a key list and a value list (of same length) to a finite map *)
Definition fromList_def :
    fromList (Xs :'a list) (Ps :('a, 'b) CCS list) = ZIP (Xs,Ps)
End

val _ = overload_on ("|->", ``fromList``);
val _ = set_fixity "|->" (Infix(NONASSOC, 100));

Theorem IN_fromList :
    !X Xs Ps. (LENGTH Ps = LENGTH Xs) ==>
              (MEM X (MAP FST (fromList Xs Ps)) <=> MEM X Xs)
Proof
    SRW_TAC [] [fromList_def, MAP_ZIP]
QED

Theorem ALOOKUP_fromList :
    !Xs Ps n. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              n < LENGTH Xs ==>
              THE (ALOOKUP (fromList Xs Ps) (EL n Xs)) = EL n Ps
Proof
    RW_TAC std_ss [fromList_def]
 >> Q.ABBREV_TAC `ls = ZIP (Xs,Ps)`
 >> Know `EL n Xs = FST (EL n ls)`
 >- (Q.UNABBREV_TAC `ls` >> rw [EL_ZIP])
 >> Rewr'
 >> Know `ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls))`
 >- (MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_EL \\
     Q.UNABBREV_TAC `ls` >> fs [MAP_ZIP, LENGTH_ZIP])
 >> Rewr'
 >> Q.UNABBREV_TAC `ls` >> fs [EL_ZIP]
QED

(* KEY result: if Xs is disjoint with free variables of E, then E{_/Xs} = E *)
Theorem CCS_SUBST_NOT_FV :
    !Xs E. DISJOINT (FV E) (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==> (CCS_Subst E (fromList Xs Ps) = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [Once CCS_SUBST_def, FV_def, IN_fromList, MAP_ZIP]
 >> Cases_on `MEM a Xs` >- fs []
 >> ASM_SIMP_TAC std_ss []
 >> Suff `DISJOINT (FV E) (set Xs)` >- METIS_TAC []
 >> ASM_SET_TAC []
QED

(* ================================================================= *)
(*   Weakly guarded equations                                        *)
(* ================================================================= *)

(* A list of variables Xs are weakly guarded in E iff:

   1. Xs is DISJOINT with the set of all bound variables (BV) used by
      recursion operators in E;
   2. For each X in Xs, if all subterms (var X) were replaced by holes,
      the resulting multi-hole context (\t. CCS_Subst E t X) is a WG.
 *)
Definition weakly_guarded_def :
    weakly_guarded Xs = \E. DISJOINT (BV E) (set Xs) /\
                            EVERY (\X. WG (\t. CCS_Subst E t X)) Xs
End

(* `context` is similar, but ... *)
Definition context_def :
    context Xs = \E. (* DISJOINT (BV E) (set Xs) /\ *)
                     EVERY (\X. CONTEXT (\t. CCS_Subst E t X)) Xs
End

Theorem EVERY_weakly_guarded :
    !Xs Es. EVERY (weakly_guarded Xs) Es ==>
            !E X. MEM E Es /\ MEM X Xs ==> WG (\t. CCS_Subst E t X)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
QED

local
  val t1 =
      MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 + E2)`, `set Xs`] >> art [BV_SUBSETS, SUBSET_REFL];
  val t2 =
      RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `WG (\t. e1 t + e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC WG4_backward;
in
  val weakly_guarded_sum = store_thm
    ("weakly_guarded_sum",
    ``!Xs E1 E2. weakly_guarded Xs (sum E1 E2) ==>
                 weakly_guarded Xs E1 /\ weakly_guarded Xs E2``,
      RW_TAC std_ss [weakly_guarded_def, EVERY_MEM] >| [t1, t2, t1, t2]);
end;

local
  val t1 =
     (MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 || E2)`, `set Xs`] >> art [BV_SUBSETS, SUBSET_REFL]);
  val t2 =
     (RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `WG (\t. e1 t || e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC WG5_backward);
in
  val weakly_guarded_par = store_thm
    ("weakly_guarded_par",
    ``!Xs E1 E2. weakly_guarded Xs (par E1 E2) ==>
                 weakly_guarded Xs E1 /\ weakly_guarded Xs E2``,
      RW_TAC std_ss [weakly_guarded_def, EVERY_MEM] >| [t1, t2, t1, t2]);
end;

Theorem weakly_guarded_restr :
    !Xs L E. weakly_guarded Xs (restr L E) ==> weakly_guarded Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. restr L (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC WG6_backward
QED

Theorem weakly_guarded_relab :
    !Xs E rf. weakly_guarded Xs (relab E rf) ==> weakly_guarded Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. relab (e t) rf)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC WG7_backward
QED

Theorem weakly_guarded_var :
    !Xs Y. weakly_guarded Xs (var Y) ==> ~MEM Y Xs
Proof
    rpt GEN_TAC
 >> Suff `MEM Y Xs ==> ~weakly_guarded Xs (var Y)` >- METIS_TAC []
 >> DISCH_TAC >> CCONTR_TAC
 >> fs [weakly_guarded_def, EVERY_MEM]
 >> RES_TAC >> fs [CCS_Subst_def, NO_WG0]
QED

(* This theorem is only possible with our special `weakly_guarded`:
   those `var Y` left in E must not be wrongly treated as free variables.
 *)
Theorem weakly_guarded_rec :
    !Xs Y E. weakly_guarded Xs (rec Y E) ==> ~MEM Y Xs /\ weakly_guarded Xs E
Proof
    rpt GEN_TAC >> DISCH_TAC >> STRONG_CONJ_TAC
 >- (fs [weakly_guarded_def, EVERY_MEM] \\
    `Y IN BV (rec Y E)` by PROVE_TAC [BV_REC] \\
     CCONTR_TAC >> METIS_TAC [IN_DISJOINT])
 >> DISCH_TAC
 >> fs [weakly_guarded_def, EVERY_MEM]
 >> rpt STRIP_TAC
 >- (MATCH_MP_TAC SUBSET_DISJOINT \\
     take [`BV (rec Y E)`, `set Xs`] >> art [BV_SUBSETS, SUBSET_REFL])
 >> RES_TAC
 >> Cases_on `Y = X` >- fs []
 >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. rec Y (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> MATCH_MP_TAC WG8_backward
 >> Q.EXISTS_TAC `Y` >> art []
QED

(* KEY result, c.f. WG8_IMP_CONST *)
Theorem weakly_guarded_rec_imp_disjoint :
    !Xs Y E. weakly_guarded Xs (rec Y E) ==> DISJOINT (FV E) (set Xs)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
 >> CCONTR_TAC >> fs [IN_DISJOINT, BV_def]
 >> RES_TAC
 >> `Y <> x` by PROVE_TAC []
 >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t x`
 >> Know `WG (\t. rec Y (e t))` >- (Q.UNABBREV_TAC `e` >> fs [])
 >> Q.PAT_X_ASSUM `WG (\t. P)` K_TAC (* clean up *)
 >> DISCH_TAC
 >> IMP_RES_TAC WG8_IMP_CONST
 >> Q.UNABBREV_TAC `e` >> fs [IS_CONST_def]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP CCS_Subst_IMP_NO_FV))
QED

(* ================================================================= *)
(*   Unique Solution of Equations                                    *)
(* ================================================================= *)

(* Lemma 4.13 in Milner's book [1] (the full version):

   If the variable X is weakly guarded in E, and E{Ps/Xs} --u-> P',
   then P' takes the form E'{Ps/Xs} (for some expression E'), and
   moreover, for any Qs, E{Qs/Xs} --u-> E'{Qs/Xs}.
 *)
Theorem strong_unique_solution_lemma : (* full version *)
    !Xs E. weakly_guarded Xs E ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==>
                !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
                       ?E'. (P' = CCS_SUBST (fromList Xs Ps) E') /\
                            !Qs. (LENGTH Qs = LENGTH Xs) ==>
                                 TRANS (CCS_SUBST (fromList Xs Qs) E) u
                                       (CCS_SUBST (fromList Xs Qs) E')
Proof
    GEN_TAC >> Induct_on `E` >> rpt STRIP_TAC (* 8 subgoals *)
 (* Case 0: E = nil, impossible *)
 >- fs [CCS_SUBST_def, NIL_NO_TRANS]
 (* Case 1: E = Y, a variable, still impossible *)
 >- (rename1 `weakly_guarded Xs (var Y)` \\
     IMP_RES_TAC weakly_guarded_var \\
    `~MEM Y (MAP FST (fromList Xs Ps))` by METIS_TAC [IN_fromList] \\
     fs [CCS_SUBST_def, VAR_NO_TRANS])
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
 (* Case 7 (difficult): E = rec Y E' *)
 >> rename1 `weakly_guarded Xs (rec Y E)`
 >> Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` K_TAC
 >> IMP_RES_TAC weakly_guarded_rec_imp_disjoint
 >> `DISJOINT (FV (rec Y E)) (set Xs)` by ASM_SET_TAC [FV_def]
 (* simplify `CCS_Subst (rec Y E) (Ps |-> Qs)` *)
 >> Know `CCS_Subst (rec Y E) (Xs |-> Ps) = rec Y E`
 >- (irule CCS_SUBST_NOT_FV >> art [])
 >> DISCH_THEN (fs o wrap)
 >> `DISJOINT (BV (rec Y E)) (set Xs)` by PROVE_TAC [weakly_guarded_def]
 (* KEY step: let E' = P' *)
 >> Q.EXISTS_TAC `P'`
 >> Suff `DISJOINT (FV P') (set Xs)`
 >- (DISCH_TAC >> CONJ_TAC
     >- (MATCH_MP_TAC EQ_SYM >> irule CCS_SUBST_NOT_FV >> art []) \\
     rpt STRIP_TAC \\
     Know `CCS_Subst (rec Y E) (Xs |-> Qs) = rec Y E`
     >- (irule CCS_SUBST_NOT_FV >> art []) >> Rewr' \\
     Know `CCS_Subst P' (Xs |-> Qs) = P'`
     >- (irule CCS_SUBST_NOT_FV >> art []) >> Rewr' \\
     ASM_REWRITE_TAC [])
 (* DISJOINT (FV P') (set Xs) *)
 >> MATCH_MP_TAC SUBSET_DISJOINT
 >> take [`FV (rec Y E) UNION BV (rec Y E)`, `set Xs`] >> art [SUBSET_REFL]
 >> CONJ_TAC >- ASM_SET_TAC []
 >> MATCH_MP_TAC TRANS_FV
 >> Q.EXISTS_TAC `u` >> art []
QED

(* NOTE: Es MUST contain free variables up to Xs *)
Definition CCS_equation_def :
    CCS_equation (Xs :'a list) (Es :('a, 'b) CCS list) <=>
        ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs) /\
        EVERY (\E. (FV E) SUBSET (set Xs)) Es
End

(* A solution Ps of the CCS equation (group) Es[Xs] up to R *)
Definition CCS_solution_def :
    CCS_solution Xs Es R Ps <=>
     (* ALL_PROC Ps /\ *)
        LIST_REL R Ps (MAP (CCS_SUBST (fromList Xs Ps)) Es)
End

val _ = overload_on ( "STRONG_EQUIV", ``LIST_REL  STRONG_EQUIV``);
val _ = overload_on (   "WEAK_EQUIV", ``LIST_REL    WEAK_EQUIV``);
val _ = overload_on (    "OBS_CONGR", ``LIST_REL     OBS_CONGR``);
val _ = overload_on ("OBS_contracts", ``LIST_REL OBS_contracts``);

(* Proposition 4.12 of [Mil89], c.f. StrongLawsTheory.STRONG_UNFOLDING

   Let Es and Fs contain (free, equation) variable Es at most. Let
   As = Es{As/Xs}, Bs = Es{Bs/Xs} and Es ~ Fs. Then As ~ Bs.

Theorem strong_equiv_presd_by_rec :
    !Xs Es Fs As Bs. CCS_equation Xs Es /\ CCS_equation Xs Fs /\
                     CCS_solution Xs Es (=) As /\
                     CCS_solution Xs Fs (=) Bs /\
                     LIST_REL STRONG_EQUIV Es Fs
                 ==> LIST_REL STRONG_EQUIV As Bs
Proof
   cheat
QED
 *)

(* Proposition 4.12 of [Mil89], the univariate version (unconfirmed):

   Let P and Q contain (free, recursion) variable X at most.
   Let A = P{A/X} (or `rec X P`), B = Q{B/X} (or `rec X Q`) and E ~ F.
   Then A ~ B.

Theorem STRONG_EQUIV_PRESD_BY_REC :
    !X P Q. (FV P) SUBSET {X} /\ (FV Q) SUBSET {X} /\
            STRONG_EQUIV P Q ==> STRONG_EQUIV (rec X P) (rec X Q)
Proof
   cheat
QED
 *)

(* THE STAGE THEOREM:
   Let the expression Es contain at most Xs, and let Xs be weakly guarded in Es,
   then:
        If Ps ~ E{Ps/Xs} and Qs ~ E{Qs/Xs} then P ~ Q.

   strong_unique_solution_lemma is used to prove this result.
 *)
Theorem strong_unique_solution :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es STRONG_EQUIV) /\
                Qs IN (CCS_solution Xs Es STRONG_EQUIV)
            ==> LIST_REL STRONG_EQUIV Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_equation_def, CCS_solution_def, EVERY_MEM,
                    LIST_REL_EL_EQN]
 >> Q.PAT_X_ASSUM `!n. n < LENGTH Qs => _` (MP_TAC o (Q.SPEC `n`))
 >> Q.PAT_X_ASSUM `!n. n < LENGTH Ps => _` (MP_TAC o (Q.SPEC `n`))
 >> RW_TAC std_ss [EL_MAP]
 >> Q.ABBREV_TAC `P = EL n Ps`
 >> Q.ABBREV_TAC `Q = EL n Qs`
 >> Q.ABBREV_TAC `E = EL n Es`
 >> Q.ABBREV_TAC `X = EL n Xs`
 >> `MEM E Es` by METIS_TAC [MEM_EL]
 >> Q.PAT_X_ASSUM `!E. MEM E Es ==> EV E SUBSET set Xs` (MP_TAC o (Q.SPEC `E`))
 >> Q.PAT_X_ASSUM `!e. MEM e Es ==> _` (MP_TAC o (Q.SPEC `E`))
 >> RW_TAC std_ss [] (* stage work *)
 >> irule (REWRITE_RULE [RSUBSET] STRONG_BISIM_UPTO_THM)
 >> Q.EXISTS_TAC `\x y. (x = y) \/
                        (?G. FV G SUBSET (set Xs) /\
                             (x = CCS_SUBST (fromList Xs Ps) G) /\
                             (y = CCS_SUBST (fromList Xs Qs) G))`
 >> BETA_TAC >> Reverse CONJ_TAC
 >- (DISJ2_TAC >> Q.EXISTS_TAC `var X` \\
     unset [`X`, `P`, `Q`] \\
     SRW_TAC [] [CCS_SUBST_def, FV_def, MEM_EL, IN_fromList] (* 5 subgoals *)
     >- (Q.EXISTS_TAC `n` >> art [])
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC ALOOKUP_fromList >> art [])
     >- METIS_TAC []
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC ALOOKUP_fromList >> art [])
     >> METIS_TAC [])
 >> REWRITE_TAC [STRONG_BISIM_UPTO]
 >> fix [`P'`, `Q'`]
 >> BETA_TAC >> STRIP_TAC (* 2 sub-goals here *)
 >- cheat
 >> 
    cheat
QED

(* THE FINAL THEOREM *)
Theorem unique_solution_of_rooted_contractions :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es OBS_contracts) /\
                Qs IN (CCS_solution Xs Es OBS_contracts)
            ==> LIST_REL OBS_CONGR Ps Qs
Proof
 (* same steps as in "strong_unique_solution" until "stage work" *)
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_equation_def, CCS_solution_def, EVERY_MEM,
                    LIST_REL_EL_EQN]
 >> Q.PAT_X_ASSUM `!n. n < LENGTH Ps => _` (MP_TAC o (Q.SPEC `n`))
 >> Q.PAT_X_ASSUM `!n. n < LENGTH Qs => _` (MP_TAC o (Q.SPEC `n`))
 >> RW_TAC std_ss [EL_MAP]
 >> Q.ABBREV_TAC `P = EL n Ps`
 >> Q.ABBREV_TAC `Q = EL n Qs`
 >> Q.ABBREV_TAC `E = EL n Es`
 >> `MEM E Es` by METIS_TAC [MEM_EL]
 >> Q.PAT_X_ASSUM `!E. MEM E Es ==> EV E SUBSET set Xs` (MP_TAC o (Q.SPEC `E`))
 >> Q.PAT_X_ASSUM `!e. MEM e Es ==> _` (MP_TAC o (Q.SPEC `E`))
 >> RW_TAC std_ss [] (* stage work *)
 >>
    cheat
QED



val _ = export_theory ();
val _ = html_theory "Multivariate";
