(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Unique Solution of CCS Equations (Multivariate Version)    *)
(*                                                                            *)
(* COPYRIGHT     : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory pred_setTheory pred_setLib listTheory finite_mapTheory;

open combinTheory arithmeticTheory; (* for o_DEF and FUNPOW *)

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory TraceTheory
     ObsCongrTheory ContractionTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory;

val _ = new_theory "Multivariate";

(* ========================================================================== *)
(*                             TABLE OF CONTENTS                              *)
(* -------------------------------------------------------------------------- *)
(*  Prologue:    Design Notes . . . . . . . . . . . . . . . . . . . . . . . . *)
(*  Section I:   Multivariate variable substitution . . . . . . . . . . . . . *)
(*  Section II:  Multivariate CCS contexts. . . . . . . . . . . . . . . . . . *)
(*  Section III: Weakly-guarded contexts. . . . . . . . . . . . . . . . . . . *)
(*  Section IV:  Unique Solution of Equations . . . . . . . . . . . . . . . . *)
(*  Section V:   Unique Solution of (Rooted) Contractions . . . . . . . . . . *)
(*  Appendix:    Bibliography and some left work. . . . . . . . . . . . L2586 *)
(* ========================================================================== *)

val lset_ss = list_ss ++ PRED_SET_ss; (* list + pred_set *)

val _ = overload_on ( "STRONG_EQUIV", ``LIST_REL  STRONG_EQUIV``);
val _ = overload_on (   "WEAK_EQUIV", ``LIST_REL    WEAK_EQUIV``);
val _ = overload_on (    "OBS_CONGR", ``LIST_REL     OBS_CONGR``);
val _ = overload_on ("OBS_contracts", ``LIST_REL OBS_contracts``);

(* hide all other possible definitions of `fromList` -- this is a common name *)
val _ = hide "fromList";

(*                         -- DESIGN NOTES --

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

(* ========================================================================== *)
(*  Section I: Multivariate Variable Substitution                             *)
(* ========================================================================== *)

(* The use of alistTheory/finite_mapTheory to get rid of substitution
   orders was suggested by Konrad Slind: (HOL-info, Oct 23, 2017):

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
   (CCS_SUBST (fm :('a |-> ('a, 'b) CCS)) nil = nil) /\
   (CCS_SUBST fm (prefix u E) = prefix u (CCS_SUBST fm E)) /\
   (CCS_SUBST fm (sum E1 E2)  = sum (CCS_SUBST fm E1)
                                    (CCS_SUBST fm E2)) /\
   (CCS_SUBST fm (par E1 E2)  = par (CCS_SUBST fm E1)
                                    (CCS_SUBST fm E2)) /\
   (CCS_SUBST fm (restr L E)  = restr L (CCS_SUBST fm E)) /\
   (CCS_SUBST fm (relab E rf) = relab (CCS_SUBST fm E) rf) /\
   (CCS_SUBST fm (var X)      = if X IN FDOM fm then fm ' X else (var X)) /\
   (CCS_SUBST fm (rec X E)    = if X IN FDOM fm
                                then (rec X (CCS_SUBST (fm \\ X) E))
                                else (rec X (CCS_SUBST fm E)))
End

(* broken into separate "axioms" *)
val [CCS_SUBST_nil,   CCS_SUBST_prefix, CCS_SUBST_sum, CCS_SUBST_par,
     CCS_SUBST_restr, CCS_SUBST_relab,  CCS_SUBST_var, CCS_SUBST_rec] =
    map save_thm
        (combine (["CCS_SUBST_nil",   "CCS_SUBST_prefix",
                   "CCS_SUBST_sum",   "CCS_SUBST_par",
                   "CCS_SUBST_restr", "CCS_SUBST_relab",
                   "CCS_SUBST_var",   "CCS_SUBST_rec"],
                  CONJUNCTS CCS_SUBST_def));

Theorem CCS_SUBST_FEMPTY :
    !E. CCS_SUBST FEMPTY E = E
Proof
    Induct_on `E` >> SRW_TAC [] [CCS_SUBST_def]
QED

(* CCS_Subst can be expressed in CCS_SUBST *)
Theorem CCS_SUBST_SING :
    !X E E'. CCS_SUBST (FEMPTY |+ (X,E')) E = CCS_Subst E E' X
Proof
    GEN_TAC >> Induct_on `E`
 >> SRW_TAC [] [CCS_SUBST_def, CCS_Subst_def]
 >> REWRITE_TAC [CCS_SUBST_FEMPTY]
QED

(* from a key list and a value list (of same length) to an alist *)
Definition fromList_def :
    fromList (Xs :'a list) (Ps :('a, 'b) CCS list) = FEMPTY |++ ZIP (Xs,Ps)
End

val _ = overload_on ("|->", ``fromList``);
val _ = set_fixity "|->" (Infix (NONASSOC, 100));

Theorem fromList_EMPTY :
    fromList [] [] = FEMPTY
Proof
    SRW_TAC [] [fromList_def, FUPDATE_LIST_THM]
QED

Theorem fromList_HD :
    !x xs y ys. ~MEM x xs /\ (LENGTH xs = LENGTH ys) ==>
                (fromList (x::xs) (y::ys) = (fromList xs ys) |+ (x,y))
Proof
    SRW_TAC [] [fromList_def, FUPDATE_LIST_THM]
 >> MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES
 >> METIS_TAC [MAP_ZIP]
QED

Theorem FDOM_fromList :
    !Xs Ps. (LENGTH Ps = LENGTH Xs) ==> (FDOM (fromList Xs Ps) = set Xs)
Proof
    SRW_TAC [] [fromList_def, FDOM_FUPDATE_LIST, MAP_ZIP]
QED

Theorem fromList_FAPPLY_HD :
    !X Xs P Ps n. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) ==>
                  ((fromList (X::Xs) (P::Ps)) ' X = P)
Proof
    RW_TAC std_ss [fromList_HD, FAPPLY_FUPDATE]
QED

Theorem fromList_FAPPLY_EL :
    !Xs Ps n. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\ n < LENGTH Xs ==>
              ((fromList Xs Ps) ' (EL n Xs) = EL n Ps)
Proof
    RW_TAC std_ss [fromList_def]
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC `n`
 >> fs [LENGTH_ZIP, MAP_ZIP]
 >> RW_TAC list_ss []
 >> CCONTR_TAC >> fs []
 >> `n < LENGTH Xs /\ m <> n` by RW_TAC arith_ss []
 >> METIS_TAC [ALL_DISTINCT_EL_IMP]
QED

Theorem fromList_FAPPLY_EL' :
    !X P Xs Ps n. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
                  n < LENGTH Xs ==>
                  ((fromList (X::Xs) (P::Ps)) ' (EL n Xs) = EL n Ps)
Proof
    RW_TAC std_ss [fromList_HD, fromList_def]
 >> Know `((FEMPTY |++ ZIP (Xs,Ps)) |+ (X,P)) = ((FEMPTY |+ (X,P)) |++ ZIP (Xs,Ps))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES \\
     fs [MAP_ZIP])
 >> Rewr'
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC `n`
 >> fs [LENGTH_ZIP, MAP_ZIP]
 >> RW_TAC list_ss []
 >> CCONTR_TAC >> fs []
 >> `n < LENGTH Xs /\ m <> n` by RW_TAC arith_ss []
 >> METIS_TAC [ALL_DISTINCT_EL_IMP]
QED

(* KEY result: if Xs is disjoint with free (and bound) variables of E,
   then E{? / Xs} = E *)
Theorem CCS_SUBST_elim :
    !Xs E. DISJOINT (FV E) (set Xs) /\ DISJOINT (BV E) (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==> (CCS_SUBST (fromList Xs Ps) E = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [Once CCS_SUBST_def, BV_def, FV_def, FDOM_fromList, MAP_ZIP]
 >> `DISJOINT (FV E) (set Xs)` by ASM_SET_TAC []
 >> METIS_TAC []
QED

(* TODO: remove `DISJOINT (BV E) (set Xs)`
Theorem CCS_SUBST_elim :
    !Xs E. DISJOINT (FV E) (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==> (CCS_SUBST (fromList Xs Ps) E = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [Once CCS_SUBST_def, BV_def, FV_def, FDOM_fromList, MAP_ZIP]
 >> `DISJOINT (FV E) (set Xs)` by ASM_SET_TAC []
 >> METIS_TAC []
QED
 *)

(* more general then CCS_SUBST_elim *)
Theorem CCS_SUBST_elim' :
    !fm E. DISJOINT (FV E) (FDOM fm) /\ DISJOINT (BV E) (FDOM fm) ==>
          (CCS_SUBST fm E = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [Once CCS_SUBST_def, BV_def, FV_def]
 >> `DISJOINT (FV E) (FDOM fm)` by ASM_SET_TAC []
 >> METIS_TAC []
QED

(* TODO: remove `DISJOINT (BV E) (set Xs)`
Theorem CCS_SUBST_elim' :
    !fm E. DISJOINT (FV E) (FDOM fm) ==> (CCS_SUBST fm E = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [Once CCS_SUBST_def, BV_def, FV_def]
 >> `DISJOINT (FV E) (FDOM fm)` by ASM_SET_TAC []
 >> METIS_TAC []
QED
 *)

(* TODO: move to alistTheory (not needed here)
Theorem ADELKEY[simp] :
    (!(x :'a). ADELKEY x ([] :('a # 'b) list) = []) /\
    (!(x :'a) (y :'b) t. ~MEM x (MAP FST t) ==> (ADELKEY x ((x,y)::t) = t))
Proof
    RW_TAC list_ss [ADELKEY_unchanged, MAP, ADELKEY_def]
 >> RW_TAC list_ss [FILTER_EQ_ID, EVERY_MEM]
 >> fs [MEM_MAP] >> METIS_TAC []
QED
 *)

(* CCS_SUBST_reduce leads to CCS_SUBST_FOLDR *)
Theorem CCS_SUBST_reduce :
    !X Xs P Ps. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
                EVERY (\e. X NOTIN (FV e)) Ps ==>
         !E E'. DISJOINT (BV E) (set (X::Xs)) /\
               (CCS_SUBST (fromList Xs Ps) E = E') ==>
               (CCS_SUBST (fromList (X::Xs) (P::Ps)) E = CCS_Subst E' P X)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `E`
 >> SRW_TAC [] [CCS_SUBST_def, FDOM_fromList, BV_def]
 >> fs [CCS_Subst_def, EVERY_MEM, fromList_FAPPLY_HD] (* up to here *)
 >> `?n. n < LENGTH Xs /\ a = EL n Xs` by PROVE_TAC [MEM_EL]
 >> Know `(fromList (X::Xs) (P::Ps)) ' a = EL n Ps`
 >- (POP_ORW >> MATCH_MP_TAC fromList_FAPPLY_EL' >> art []) >> Rewr'
 >> MATCH_MP_TAC EQ_SYM
 >> Know `(fromList Xs Ps) ' a = EL n Ps`
 >- (POP_ORW >> MATCH_MP_TAC fromList_FAPPLY_EL >> art []) >> Rewr'
 >> MATCH_MP_TAC (EQ_IMP_LR CCS_Subst_elim)
 >> `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL]
 >> METIS_TAC []
QED

(* CCS_SUBST_reduce in another form *)
val lemma1 = Q.prove (
   `!E E' map. map <> [] /\
          ~MEM (FST (HD map)) (MAP FST (TL map)) /\ ALL_DISTINCT (MAP FST (TL map)) /\
          EVERY (\e. (FST (HD map)) NOTIN (FV e)) (MAP SND (TL map)) /\
          DISJOINT (BV E) (set (MAP FST map)) /\
         (CCS_SUBST (FEMPTY |++ (TL map)) E = E')
     ==> (CCS_SUBST (FEMPTY |++ map) E = CCS_Subst E' (SND (HD map)) (FST (HD map)))`,
 (* proof *)
    rpt GEN_TAC
 >> Cases_on `map` >- SRW_TAC [] []
 >> RW_TAC std_ss [HD, TL]
 >> Cases_on `h` >> fs []
 >> rename1 `X NOTIN (BV E)`
 >> Q.ABBREV_TAC `Xs = FST (UNZIP t)`
 >> Q.ABBREV_TAC `Ps = SND (UNZIP t)`
 >> Know `t = ZIP (Xs,Ps)` >- (unset [`Xs`, `Ps`] >> fs [])
 >> Know `LENGTH Ps = LENGTH Xs` >- (unset [`Xs`, `Ps`] >> fs [])
 >> RW_TAC std_ss []
 >> Know `(MAP FST (ZIP (Xs,Ps))) = Xs` >- PROVE_TAC [MAP_ZIP]
 >> DISCH_THEN (fs o wrap)
 >> Know `(MAP SND (ZIP (Xs,Ps))) = Ps` >- PROVE_TAC [MAP_ZIP]
 >> DISCH_THEN (fs o wrap)
 >> MP_TAC (REWRITE_RULE [fromList_def] (Q.SPECL [`X`,`Xs`,`r`,`Ps`] CCS_SUBST_reduce))
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [ZIP, LIST_TO_SET]) o (Q.SPEC `E`))
 >> `DISJOINT (BV E) (X INSERT (set Xs))` by ASM_SET_TAC []
 >> RW_TAC std_ss []);

(* Let map = ZIP(Xs,Ps), to convert CCS_SUBST to a folding of CCS_Subst, each P
   of Ps must contains free variables up to the corresponding X of Xs.
 *)
val lemma2 = Q.prove (
   `!E map. ALL_DISTINCT (MAP FST map) /\
            EVERY (\(x,p). FV p SUBSET {x}) map /\
            DISJOINT (BV E) (set (MAP FST map)) ==>
           (CCS_SUBST (FEMPTY |++ map) E = FOLDR (\l e. CCS_Subst e (SND l) (FST l)) E map)`,
 (* proof *)
    GEN_TAC >> Induct_on `map`
 >- SRW_TAC [] [FUPDATE_LIST_THM, CCS_SUBST_FEMPTY]
 >> rpt STRIP_TAC >> fs [MAP]
 >> MP_TAC (Q.SPECL [`E`, `CCS_SUBST (FEMPTY |++ map) E`,
                     `h::map`] lemma1) >> fs []
 >> Cases_on `h` >> fs []
 >> rename1 `X NOTIN (BV E)`
 >> rename1 `FV P SUBSET {X}`
 >> Know `EVERY (\e. X NOTIN (FV e)) (MAP SND map)`
 >- (fs [EVERY_MEM] >> RW_TAC std_ss [] \\
     fs [MEM_MAP] \\
    `X <> FST y` by METIS_TAC [] \\
     CCONTR_TAC >> fs [] >> RES_TAC \\
     Cases_on `y` >> fs [] >> ASM_SET_TAC [])
 >> RW_TAC std_ss []);

(* lemma2 in another form; this is less general than CCS_SUBST_reduce *)
Theorem CCS_SUBST_FOLDR :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              EVERY (\(x,p). FV p SUBSET {x}) (ZIP (Xs,Ps)) /\
              DISJOINT (BV E) (set Xs) ==>
             (CCS_SUBST (fromList Xs Ps) E =
              FOLDR (\(x,y) e. CCS_Subst e y x) E (ZIP (Xs,Ps)))
Proof
    RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`E`, `ZIP (Xs,Ps)`] lemma2)
 >> RW_TAC std_ss [MAP_ZIP, fromList_def]
 >> KILL_TAC
 >> Suff `(\l e. CCS_Subst e (SND l) (FST l)) = (\(x,y) e. CCS_Subst e y x)`
 >- SIMP_TAC std_ss []
 >> rw [FUN_EQ_THM]
 >> Cases_on `l` >> rw []
QED

(* A FOLDL-like version of CCS_SUBST_reduce
Theorem CCS_SUBST_reduce' :
    !E X P Xs Ps. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
                  EVERY (\(x,p). FV p SUBSET {x}) (ZIP (Xs,Ps)) /\
                  DISJOINT (BV E) (set (X::Xs)) ==>
                 (CCS_SUBST (fromList (X::Xs) (P::Ps)) E =
                  CCS_SUBST (fromList Xs Ps) (CCS_Subst E P X))
Proof
    NTAC 3 GEN_TAC
 >> Induct_on `Xs` >> SRW_TAC [][]
QED
 *)

(* `ALL_DISTINCT Xs` is not necessary but makes the proof (much) easier;
   `DISJOINT (BV E) (set Xs)` is also not necessary but without it
    the proof (mostly dependent lemmas) cannot complete.
 *)
Theorem CCS_SUBST_self :
    !E Xs. ALL_DISTINCT Xs /\ DISJOINT (BV E) (set Xs) ==>
           (CCS_SUBST (fromList Xs (MAP var Xs)) E = E)
Proof
    GEN_TAC >> Induct_on `Xs`
 >> SRW_TAC [] [CCS_SUBST_FEMPTY, fromList_EMPTY]
 >> Q.PAT_X_ASSUM `ALL_DISTINCT Xs /\ DISJOINT (BV E) (set Xs) ==> _` MP_TAC
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`h`, `Xs`, `var h`, `MAP var Xs`] CCS_SUBST_reduce)
 >> `LENGTH (MAP var Xs) = LENGTH Xs` by PROVE_TAC [LENGTH_MAP]
 >> Suff `EVERY (\e. h NOTIN FV e) (MAP var Xs)` >- fs []
 >> RW_TAC std_ss [EVERY_MEM, MEM_MAP]
 >> ASM_SET_TAC [FV_def]
QED

(* KEY result. `DISJOINT (BV C) (set Xs)` (usually from `context Xs C`)
   is not really necessary but makes the proof (much) easier.
 *)
Theorem CCS_SUBST_nested :
    !Xs Ps Es C.
        ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\ (LENGTH Es = LENGTH Xs) /\
        DISJOINT (BV C) (set Xs) ==>
       (CCS_SUBST (fromList Xs Ps) (CCS_SUBST (fromList Xs Es) C) =
        CCS_SUBST (fromList Xs (MAP (CCS_SUBST (Xs |-> Ps)) Es)) C)
Proof
    Suff (* rewriting for induction *)
   `!Xs Ps Es. ALL_DISTINCT Xs /\
              (LENGTH Ps = LENGTH Xs) /\ (LENGTH Es = LENGTH Xs) ==>
        !C. DISJOINT (BV C) (set Xs) ==>
            (CCS_SUBST (fromList Xs Ps)
                       (CCS_SUBST (fromList Xs Es) C) =
             CCS_SUBST (fromList Xs (MAP (CCS_SUBST (Xs |-> Ps)) Es)) C)`
 >- METIS_TAC []
 >> rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `C` (* 8 subgoals *)
 >- RW_TAC std_ss [CCS_SUBST_nil]
 >- (RW_TAC lset_ss [BV_def, CCS_SUBST_var, FDOM_fromList, LENGTH_MAP] \\
     fs [MEM_EL] >> rename1 `X = EL n Xs` \\
    `LENGTH (MAP (CCS_SUBST (fromList Xs Ps)) Es) = LENGTH Xs`
       by PROVE_TAC [LENGTH_MAP] \\
     ASM_SIMP_TAC std_ss [fromList_FAPPLY_EL, EL_MAP])
 >- RW_TAC std_ss [BV_def, CCS_SUBST_prefix]
 >- (RW_TAC std_ss [BV_def, CCS_SUBST_sum] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC [])
 >- (RW_TAC std_ss [BV_def, CCS_SUBST_par] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC [])
 >- RW_TAC std_ss [BV_def, CCS_SUBST_restr]
 >- RW_TAC std_ss [BV_def, CCS_SUBST_relab]
 (* The last goal is hard *)
 >> RW_TAC std_ss [BV_def]
 >> `DISJOINT (BV C') (set Xs)` by ASM_SET_TAC [SUBSET_DISJOINT]
 >> RES_TAC
 >> `LENGTH (MAP (CCS_SUBST (fromList Xs Ps)) Es) = LENGTH Xs`
       by PROVE_TAC [LENGTH_MAP]
 >> RW_TAC list_ss [CCS_SUBST_rec, FDOM_fromList, LENGTH_MAP]
 >> ASM_SET_TAC []
QED

(* Now consider a (non-trivial) generalization of FV_SUBSET and BV_SUBSET:

   [FV_SUBSET]  Theorem      
      ⊢ !X E E'. FV (CCS_Subst E E' X) SUBSET FV E UNION FV E'

   [BV_SUBSET]  Theorem
      ⊢ !X E E'. BV (CCS_Subst E E' X) SUBSET BV E UNION BV E'

   If, instead of just substituting one (free) variable of E, we
   substitute more of them, can we say that:

   [FV_SUBSET_BIGUNION]
   |- !Xs Ps E. FV (CCS_SUBST (Xs |-> Ps) E) SUBSET
                (FV E) UNION BIGUNION (IMAGE FV (set Ps))`

   and

   [BV_SUBSET_BIGUNION]
   |- !Xs Ps E. BV (CCS_SUBST (Xs |-> Ps) E) SUBSET
                (BV E) UNION BIGUNION (IMAGE BV (set Ps))` hold?
 *)

(* `ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs)` is not really necessary
   but makes the proof (much) easier.

  `DISJOINT (BV E) (set Xs)` (usually comes from `context Xs E`
   or `weakly_guarded Xs E`) is also not necessary but makes the
   proof even more easier.
 *)
Theorem BV_SUBSET_BIGUNION :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              DISJOINT (BV E) (set Xs) ==>
              BV (CCS_SUBST (fromList Xs Ps) E) SUBSET
                 (BV E) UNION BIGUNION (IMAGE BV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_SUBST_def, BV_def, FDOM_fromList] (* 6 subgoals *)
 >- (fs [MEM_EL, fromList_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] >> ASM_SET_TAC [])
 (* 5 subgoals left ... *)
 >> ASM_SET_TAC []
QED

Theorem FV_SUBSET_BIGUNION :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              DISJOINT (BV E) (set Xs) ==>
              FV (CCS_SUBST (fromList Xs Ps) E) SUBSET
                 (FV E) UNION BIGUNION (IMAGE FV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_SUBST_def, FV_def, BV_def, FDOM_fromList] (* 6 subgoals *)
 >- (fs [MEM_EL, fromList_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] >> ASM_SET_TAC [])
 (* 5 subgoals left ... *)
 >> ASM_SET_TAC [] 
QED

(* A more precise estimation with `set Xs` *)
Theorem FV_SUBSET_BIGUNION_PRO :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              DISJOINT (BV E) (set Xs) ==>
              FV (CCS_SUBST (fromList Xs Ps) E) SUBSET
                 ((FV E) DIFF (set Xs)) UNION BIGUNION (IMAGE FV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_SUBST_def, FV_def, BV_def, FDOM_fromList] (* 6 subgoals *)
 >- (fs [MEM_EL, fromList_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] \\
     ASM_SET_TAC [])
 (* 5 subgoals left ... *)
 >- (Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC
       `FV E DIFF set Xs UNION BIGUNION (IMAGE FV (set Ps))` >> art [] \\
     SET_TAC [])
 >- (Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC
       `FV E' DIFF set Xs UNION BIGUNION (IMAGE FV (set Ps))` >> art [] \\
     SET_TAC [])
 >- (Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC
       `FV E DIFF set Xs UNION BIGUNION (IMAGE FV (set Ps))` >> art [] \\
     SET_TAC [])
 >- (Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC
       `FV E' DIFF set Xs UNION BIGUNION (IMAGE FV (set Ps))` >> art [] \\
     SET_TAC [])
 >> Q.PAT_X_ASSUM `_ ==> _ SUBSET _` MP_TAC >> RW_TAC bool_ss []
 >> ASM_SET_TAC [] (* ?! *)
QED

(* KEY result *)
Theorem CCS_SUBST_IS_PROC :
    !Xs Ps E. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
              ALL_PROC Ps /\ FV E SUBSET (set Xs) /\
              DISJOINT (BV E) (set Xs) ==>
              IS_PROC (CCS_SUBST (fromList Xs Ps) E)
Proof
    RW_TAC lset_ss [IS_PROC_def, ALL_PROC_def, EVERY_MEM]
 >> Suff `FV (CCS_SUBST (fromList Xs Ps) E) SUBSET {}` >- SET_TAC []
 >> Know `FV (CCS_SUBST (fromList Xs Ps) E) SUBSET
           ((FV E) DIFF (set Xs)) UNION BIGUNION (IMAGE FV (set Ps))`
 >- PROVE_TAC [FV_SUBSET_BIGUNION_PRO]
 >> Know `FV E DIFF (set Xs) = {}` >- ASM_SET_TAC [] >> Rewr'
 >> Know `BIGUNION (IMAGE FV (set Ps)) = {}`
 >- rw [NOT_IN_EMPTY, IN_BIGUNION_IMAGE, IMAGE_EQ_SING] >> Rewr'
 >> REWRITE_TAC [UNION_EMPTY]
QED

(* ========================================================================== *)
(*  Section II: Multivariate CCS contexts                                     *)
(* ========================================================================== *)

Definition context_def :
    context Xs = \E. DISJOINT (BV E) (set Xs) /\
                     EVERY (\X. CONTEXT (\t. CCS_Subst E t X)) Xs
End

Theorem context_nil :
    !Xs. context Xs nil
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def,
                   DISJOINT_EMPTY, CONTEXT2]
QED

Theorem context_prefix :
    !Xs u E. context Xs (prefix u E) ==> context Xs E
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. prefix u (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC CONTEXT3_backward
QED

Theorem context_prefix_rule :
    !Xs u E. context Xs E ==> context Xs (prefix u E)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. prefix u (e t))`
 >- (MATCH_MP_TAC CONTEXT3 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem context_prefix_rewrite :
    !Xs u E. context Xs (prefix u E) <=> context Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC context_prefix
 >> MATCH_MP_TAC context_prefix_rule >> art []
QED

local
  val t1 =
     (MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 + E2)`, `set Xs`] >> art [BV_SUBSET_rules, SUBSET_REFL]);
  val t2 =
     (RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `CONTEXT (\t. e1 t + e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC CONTEXT4_backward);
in
  val context_sum = store_thm
    ("context_sum",
    ``!Xs E1 E2. context Xs (sum E1 E2) ==> context Xs E1 /\ context Xs E2``,
      RW_TAC std_ss [context_def, EVERY_MEM] >| [t1, t2, t1, t2]);
end;

Theorem context_sum_rule :
    !Xs E1 E2. context Xs E1 /\ context Xs E2 ==> context Xs (sum E1 E2)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >- ASM_SET_TAC []
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `CONTEXT (\t. e1 t) /\ CONTEXT (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. e1 t + e2 t)`
 >- (MATCH_MP_TAC CONTEXT4 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem context_sum_rewrite :
    !Xs E1 E2. context Xs (sum E1 E2) <=>
               context Xs E1 /\ context Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC context_sum >> art [])
 >> MATCH_MP_TAC context_sum_rule >> art []
QED

local
  val t1 =
     (MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 || E2)`, `set Xs`] >> art [BV_SUBSET_rules, SUBSET_REFL]);
  val t2 =
     (RES_TAC >> fs [CCS_Subst_def] \\
      Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X` \\
      Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X` \\
      Know `CONTEXT (\t. e1 t || e2 t)`
      >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
          ASM_SIMP_TAC bool_ss []) \\
      DISCH_TAC >> IMP_RES_TAC CONTEXT5_backward);
in
  val context_par = store_thm
    ("context_par",
    ``!Xs E1 E2. context Xs (par E1 E2) ==> context Xs E1 /\ context Xs E2``,
      RW_TAC std_ss [context_def, EVERY_MEM] >| [t1, t2, t1, t2]);
end;

Theorem context_par_rule :
    !Xs E1 E2. context Xs E1 /\ context Xs E2 ==> context Xs (par E1 E2)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >- ASM_SET_TAC []
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `CONTEXT (\t. e1 t) /\ CONTEXT (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. e1 t || e2 t)`
 >- (MATCH_MP_TAC CONTEXT5 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem context_par_rewrite :
    !Xs E1 E2. context Xs (par E1 E2) <=>
               context Xs E1 /\ context Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC context_par >> art [])
 >> MATCH_MP_TAC context_par_rule >> art []
QED

Theorem context_restr :
    !Xs L E. context Xs (restr L E) ==> context Xs E
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. restr L (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC CONTEXT6_backward
QED

Theorem context_restr_rule :
    !Xs L E. context Xs E ==> context Xs (restr L E)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. restr L (e t))`
 >- (MATCH_MP_TAC CONTEXT6 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem context_restr_rewrite :
    !Xs L E. context Xs (restr L E) <=> context Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC context_restr
 >> MATCH_MP_TAC context_restr_rule >> art []
QED

Theorem context_relab :
    !Xs E rf. context Xs (relab E rf) ==> context Xs E
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. relab (e t) rf)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC CONTEXT7_backward
QED

Theorem context_relab_rule :
    !Xs E rf. context Xs E ==> context Xs (relab E rf)
Proof
    RW_TAC std_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `CONTEXT (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `CONTEXT (\t. relab (e t) rf)`
 >- (MATCH_MP_TAC CONTEXT7 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem context_relab_rewrite :
    !Xs E rf. context Xs (relab E rf) <=> context Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC context_relab
 >> MATCH_MP_TAC context_relab_rule >> art []
QED

Theorem context_var :
    !Xs Y. context Xs (var Y)
Proof
    RW_TAC lset_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> Cases_on `Y = X` >> fs [CONTEXT_rules]
QED

(* `~MEM Y Xs` doesn't hold. *)
Theorem context_rec :
    !Xs Y E. context Xs (rec Y E) ==>
             context Xs E /\ DISJOINT (FV E) (set Xs)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> CONJ_TAC
 >- (fs [context_def, EVERY_MEM, BV_def] \\
     rpt STRIP_TAC \\
     RES_TAC \\
     Cases_on `Y = X` >- fs [] \\
     fs [CCS_Subst_def] \\
     Q.ABBREV_TAC `e = \t. CCS_Subst E t X` \\
     Know `CONTEXT (\t. rec Y (e t))`
     >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC std_ss []) \\
     DISCH_TAC \\
     MATCH_MP_TAC CONTEXT8_backward \\
     Q.EXISTS_TAC `Y` >> art [])
 >> fs [context_def, EVERY_MEM]
 >> CCONTR_TAC >> fs [IN_DISJOINT, BV_def]
 >> RES_TAC
 >> `Y <> x` by PROVE_TAC []
 >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t x`
 >> Know `CONTEXT (\t. rec Y (e t))` >- (Q.UNABBREV_TAC `e` >> fs [])
 >> Q.PAT_X_ASSUM `CONTEXT (\t. P)` K_TAC (* cleanup *)
 >> DISCH_TAC
 >> IMP_RES_TAC CONTEXT8_IMP_CONST
 >> Q.UNABBREV_TAC `e` >> fs [IS_CONST_def]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP CCS_Subst_IMP_NO_FV))
QED

(* a collection of all (forward) rules of `context` *)
val context_rules = save_thm
  ("context_rules",
    LIST_CONJ [context_nil, context_var, context_prefix_rule,
               context_sum_rule, context_par_rule,
               context_restr_rule, context_relab_rule]);

(* a collection of all backward rules of `context` *)
val context_backward_rules = save_thm
  ("context_backward_rules",
    LIST_CONJ [context_prefix, context_sum, context_par,
               context_restr, context_relab, context_rec]);

(* c.f. STRONG_EQUIV_SUBST_CONTEXT *)
Theorem STRONG_EQUIV_subst_context :
    !Xs Ps Qs. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
               LIST_REL STRONG_EQUIV Ps Qs ==>
        !E. context Xs E ==>
            STRONG_EQUIV (CCS_SUBST (fromList Xs Ps) E)
                         (CCS_SUBST (fromList Xs Qs) E)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `E` >> RW_TAC lset_ss [CCS_SUBST_def] (* 14 subgoals *)
 >- REWRITE_TAC [STRONG_EQUIV_REFL]
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL])
 (* impossible case *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* impossible case *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 10 cases left *)
 >- REWRITE_TAC [STRONG_EQUIV_REFL]
 (* 9 cases left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_prefix)
 (* 8 cases left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_SUM \\
     IMP_RES_TAC context_sum \\
     RES_TAC >> art [])
 (* 7 cases left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
     IMP_RES_TAC context_par \\
     RES_TAC >> art [])
 (* 6 cases left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_restr)
 (* 5 cases left *)
 >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_relab)
 (* 4 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST ((fromList Xs Ps) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     Know `CCS_SUBST ((fromList Xs Qs) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     REWRITE_TAC [STRONG_EQUIV_REFL])
 (* 3 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST ((fromList Xs Ps) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     REWRITE_TAC [STRONG_EQUIV_REFL])
 (* 2 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     Know `CCS_SUBST ((fromList Xs Qs) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     REWRITE_TAC [STRONG_EQUIV_REFL])
 >> (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     REWRITE_TAC [STRONG_EQUIV_REFL])
QED

(* c.f. OBS_CONGR_SUBST_CONTEXT *)
Theorem OBS_CONGR_subst_context :
    !Xs Ps Qs. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
               LIST_REL OBS_CONGR Ps Qs ==>
        !E. context Xs E ==>
            OBS_CONGR (CCS_SUBST (fromList Xs Ps) E)
                      (CCS_SUBST (fromList Xs Qs) E)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `E` >> RW_TAC lset_ss [CCS_SUBST_def] (* 14 subgoals *)
 >- REWRITE_TAC [OBS_CONGR_REFL]
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL])
 (* impossible case *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* impossible case *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 10 cases left *)
 >- REWRITE_TAC [OBS_CONGR_REFL]
 (* 9 cases left *)
 >- (MATCH_MP_TAC OBS_CONGR_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_prefix)
 (* 8 cases left *)
 >- (MATCH_MP_TAC OBS_CONGR_PRESD_BY_SUM \\
     IMP_RES_TAC context_sum \\
     RES_TAC >> art [])
 (* 7 cases left *)
 >- (MATCH_MP_TAC OBS_CONGR_PRESD_BY_PAR \\
     IMP_RES_TAC context_par \\
     RES_TAC >> art [])
 (* 6 cases left *)
 >- (MATCH_MP_TAC OBS_CONGR_SUBST_RESTR \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_restr)
 (* 5 cases left *)
 >- (MATCH_MP_TAC OBS_CONGR_SUBST_RELAB \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_relab)
 (* 4 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST ((fromList Xs Ps) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     Know `CCS_SUBST ((fromList Xs Qs) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     REWRITE_TAC [OBS_CONGR_REFL])
 (* 3 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST ((fromList Xs Ps) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     REWRITE_TAC [OBS_CONGR_REFL])
 (* 2 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     Know `CCS_SUBST ((fromList Xs Qs) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     REWRITE_TAC [OBS_CONGR_REFL])
 >> (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     REWRITE_TAC [OBS_CONGR_REFL])
QED

(* c.f. OBS_contracts_SUBST_CONTEXT *)
Theorem OBS_contracts_subst_context :
    !Xs Ps Qs. ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) /\
               LIST_REL OBS_contracts Ps Qs ==>
        !E. context Xs E ==>
            OBS_contracts (CCS_SUBST (fromList Xs Ps) E)
                          (CCS_SUBST (fromList Xs Qs) E)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `E` >> RW_TAC lset_ss [CCS_SUBST_def] (* 14 subgoals *)
 >- REWRITE_TAC [OBS_contracts_REFL]
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     fs [FDOM_fromList, MEM_EL, LIST_REL_EL_EQN] \\
     rw [fromList_FAPPLY_EL])
 (* impossible case *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* impossible case *)
 >- (`LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
     METIS_TAC [FDOM_fromList])
 (* 10 cases left *)
 >- REWRITE_TAC [OBS_contracts_REFL]
 (* 9 cases left *)
 >- (MATCH_MP_TAC OBS_contracts_SUBST_PREFIX \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_prefix)
 (* 8 cases left *)
 >- (MATCH_MP_TAC OBS_contracts_PRESD_BY_SUM \\
     IMP_RES_TAC context_sum \\
     RES_TAC >> art [])
 (* 7 cases left *)
 >- (MATCH_MP_TAC OBS_contracts_PRESD_BY_PAR \\
     IMP_RES_TAC context_par \\
     RES_TAC >> art [])
 (* 6 cases left *)
 >- (MATCH_MP_TAC OBS_contracts_SUBST_RESTR \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_restr)
 (* 5 cases left *)
 >- (MATCH_MP_TAC OBS_contracts_SUBST_RELAB \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     IMP_RES_TAC context_relab)
 (* 4 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST ((fromList Xs Ps) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     Know `CCS_SUBST ((fromList Xs Qs) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     REWRITE_TAC [OBS_contracts_REFL])
 (* 3 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST ((fromList Xs Ps) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     REWRITE_TAC [OBS_contracts_REFL])
 (* 2 cases left *)
 >- (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     Know `CCS_SUBST ((fromList Xs Qs) \\ a) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC []) >> Rewr' \\
     REWRITE_TAC [OBS_contracts_REFL])
 >> (IMP_RES_TAC context_rec \\
    `DISJOINT (BV E) (set Xs)` by PROVE_TAC [context_def] \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
        `LENGTH Qs = LENGTH Xs` by METIS_TAC [LIST_REL_LENGTH] \\
         ASM_SIMP_TAC std_ss [FDOM_fromList]) >> Rewr' \\
     REWRITE_TAC [OBS_contracts_REFL])
QED

(* KEY result: multivariate version of CongruenceTheory.CONTEXT_combin *)
Theorem context_combin :
    !Xs Es C. ALL_DISTINCT Xs /\ context Xs C /\
              EVERY (context Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
              context Xs (CCS_SUBST (fromList Xs Es) C)
Proof
    Suff `!Xs. ALL_DISTINCT Xs ==>
               !Es C. context Xs C ==>
                      EVERY (context Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
                      context Xs (CCS_SUBST (fromList Xs Es) C)` >- METIS_TAC []
 >> NTAC 3 STRIP_TAC
 >> Induct_on `C` >> RW_TAC std_ss [CCS_SUBST_def] (* 8 subgoals *)
 (* goal 1 (of 8): not easy *)
 >- (Know `FDOM (fromList Xs Es) = set Xs`
     >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap) \\
     fs [EVERY_MEM, MEM_EL] \\
     Know `(fromList Xs Es) ' (EL n Xs) = EL n Es`
     >- (MATCH_MP_TAC fromList_FAPPLY_EL >> art []) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> art [])
 (* goal 2 (of 8): easy *)
 >- (Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     IMP_RES_TAC context_prefix >> RES_TAC \\
     MATCH_MP_TAC context_prefix_rule >> art [])
 (* goal 3 (of 8): easy *)
 >- (IMP_RES_TAC context_sum \\
     Q.PAT_X_ASSUM `context Xs C'' ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_sum_rule >> art [])
 (* goal 4 (of 8): easy *)
 >- (IMP_RES_TAC context_par \\
     Q.PAT_X_ASSUM `context Xs C'' ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_par_rule >> art [])
 (* goal 5 (of 8): easy *)
 >- (IMP_RES_TAC context_restr \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_restr_rule >> art [])
 (* goal 6 (of 8): easy *)
 >- (IMP_RES_TAC context_relab \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC context_relab_rule >> art [])
 (* goal 7 (of 8): hard *)
 >- (Know `FDOM (fromList Xs Es) = set Xs`
     >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap) \\
     IMP_RES_TAC context_rec \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     rename1 `MEM X Xs` \\
     Suff `CCS_SUBST ((fromList Xs Es) \\ X) C' = C'` >- fs [] \\
     MATCH_MP_TAC CCS_SUBST_elim' \\
     ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
     ASM_SET_TAC [context_def])
 (* goal 8 (of 8): not hard *)
 >> Know `FDOM (fromList Xs Es) = set Xs`
 >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap)
 >> IMP_RES_TAC context_rec
 >> Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss []
 >> Know `CCS_SUBST (fromList Xs Es) C' = C'`
 >- (irule CCS_SUBST_elim >> fs [context_def])
 >> DISCH_THEN (fs o wrap)
QED

Theorem LIST_REL_equivalence : (* unused *)
    !R. equivalence R ==> equivalence (LIST_REL R)
Proof
    RW_TAC list_ss [equivalence_def, reflexive_def, symmetric_def,
                    transitive_def, LIST_REL_EL_EQN]
 >- (EQ_TAC >> RW_TAC std_ss [])
 >> Q.PAT_X_ASSUM `!x y z. R x y /\ R y z ==> R x z` MATCH_MP_TAC
 >> Q.EXISTS_TAC `EL n y`
 >> CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* ========================================================================== *)
(*  Section III: Weakly guarded equations                                     *)
(* ========================================================================== *)

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

Theorem weakly_guarded_imp_context :
    !Xs E. weakly_guarded Xs E ==> context Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, context_def, EVERY_MEM]
 >> MATCH_MP_TAC WG_IMP_CONTEXT
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem EVERY_weakly_guarded :
    !Xs Es. EVERY (weakly_guarded Xs) Es ==>
            !E X. MEM E Es /\ MEM X Xs ==> WG (\t. CCS_Subst E t X)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM]
QED

Theorem weakly_guarded_nil :
    !Xs. weakly_guarded Xs nil
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def, CCS_Subst_def,
                   DISJOINT_EMPTY, WG2]
QED

Theorem weakly_guarded_prefix :
    !Xs u E. weakly_guarded Xs (prefix u E) ==> context Xs E
Proof
    RW_TAC std_ss [weakly_guarded_def, context_def, EVERY_MEM, BV_def]
 >> RES_TAC >> fs [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. prefix u (e t))`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC >> IMP_RES_TAC WG3_backward
QED

Theorem weakly_guarded_prefix_rule :
    !Xs u E. context Xs E ==> weakly_guarded Xs (prefix u E)
Proof
    RW_TAC std_ss [weakly_guarded_def, context_def, EVERY_MEM, BV_def]
 >> RES_TAC >> rw [CCS_Subst_def]
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. prefix u (CCS_Subst E t X)) = WG (\t. prefix u (e t))`
 >- (Q.UNABBREV_TAC `e` >> rw []) >> Rewr'
 >> MATCH_MP_TAC WG3 >> art []
QED

local
  val t1 =
      MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 + E2)`, `set Xs`] >> art [BV_SUBSET_rules, SUBSET_REFL];
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

Theorem weakly_guarded_sum_rule :
    !Xs E1 E2. weakly_guarded Xs E1 /\ weakly_guarded Xs E2 ==>
               weakly_guarded Xs (sum E1 E2)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >- ASM_SET_TAC []
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `WG (\t. e1 t) /\ WG (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. e1 t + e2 t)`
 >- (MATCH_MP_TAC WG4 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_sum_rewrite :
    !Xs E1 E2. weakly_guarded Xs (sum E1 E2) <=>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC weakly_guarded_sum >> art [])
 >> MATCH_MP_TAC weakly_guarded_sum_rule >> art []
QED

local
  val t1 =
     (MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 || E2)`, `set Xs`] >> art [BV_SUBSET_rules, SUBSET_REFL]);
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

Theorem weakly_guarded_par_rule :
    !Xs E1 E2. weakly_guarded Xs E1 /\ weakly_guarded Xs E2 ==>
               weakly_guarded Xs (par E1 E2)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >- ASM_SET_TAC []
 >> RES_TAC
 >> Q.ABBREV_TAC `e1 = \t. CCS_Subst E1 t X`
 >> Q.ABBREV_TAC `e2 = \t. CCS_Subst E2 t X`
 >> Know `WG (\t. e1 t) /\ WG (\t. e2 t)`
 >- (Q.UNABBREV_TAC `e1` >> Q.UNABBREV_TAC `e2` \\
     ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. e1 t || e2 t)`
 >- (MATCH_MP_TAC WG5 >> art [])
 >> unset [`e1`, `e2`] >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_par_rewrite :
    !Xs E1 E2. weakly_guarded Xs (par E1 E2) <=>
               weakly_guarded Xs E1 /\ weakly_guarded Xs E2
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (IMP_RES_TAC weakly_guarded_par >> art [])
 >> MATCH_MP_TAC weakly_guarded_par_rule >> art []
QED

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

Theorem weakly_guarded_restr_rule :
    !Xs L E. weakly_guarded Xs E ==> weakly_guarded Xs (restr L E)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. restr L (e t))`
 >- (MATCH_MP_TAC WG6 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_restr_rewrite :
    !Xs L E. weakly_guarded Xs (restr L E) <=> weakly_guarded Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC weakly_guarded_restr
 >> MATCH_MP_TAC weakly_guarded_restr_rule >> art []
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

Theorem weakly_guarded_relab_rule :
    !Xs E rf. weakly_guarded Xs E ==> weakly_guarded Xs (relab E rf)
Proof
    RW_TAC std_ss [weakly_guarded_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> RES_TAC
 >> Q.ABBREV_TAC `e = \t. CCS_Subst E t X`
 >> Know `WG (\t. e t)`
 >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC bool_ss [])
 >> DISCH_TAC
 >> Know `WG (\t. relab (e t) rf)`
 >- (MATCH_MP_TAC WG7 >> art [])
 >> Q.UNABBREV_TAC `e` >> SIMP_TAC std_ss []
QED

Theorem weakly_guarded_relab_rewrite :
    !Xs E rf. weakly_guarded Xs (relab E rf) <=> weakly_guarded Xs E
Proof
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >- IMP_RES_TAC weakly_guarded_relab
 >> MATCH_MP_TAC weakly_guarded_relab_rule >> art []
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

Theorem weakly_guarded_var_rule :
    !Xs Y. ~MEM Y Xs ==> weakly_guarded Xs (var Y)
Proof
    RW_TAC lset_ss [weakly_guarded_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> Cases_on `Y = X` >> fs [WG_rules]
QED

(* This theorem is only possible with our special `weakly_guarded`:
   those `var Y` left in E must not be wrongly treated as free variables.
 *)
Theorem weakly_guarded_rec :
    !Xs Y E. weakly_guarded Xs (rec Y E) ==>
             ~MEM Y Xs /\ DISJOINT (FV E) (set Xs) /\ weakly_guarded Xs E
Proof
 (* Part I *)
    rpt GEN_TAC >> DISCH_TAC >> STRONG_CONJ_TAC
 >- (fs [weakly_guarded_def, EVERY_MEM] \\
    `Y IN BV (rec Y E)` by PROVE_TAC [BV_REC] \\
     CCONTR_TAC >> METIS_TAC [IN_DISJOINT])
 >> DISCH_TAC
 (* Part II (not used) *)
 >> Reverse CONJ_TAC
 >- (fs [weakly_guarded_def, EVERY_MEM] \\
     rpt STRIP_TAC
     >- (MATCH_MP_TAC SUBSET_DISJOINT \\
         take [`BV (rec Y E)`, `set Xs`] >> art [BV_SUBSET_rules, SUBSET_REFL]) \\
     RES_TAC \\
     Cases_on `Y = X` >- fs [] \\
     fs [CCS_Subst_def] \\
     Q.ABBREV_TAC `e = \t. CCS_Subst E t X` \\
     Know `WG (\t. rec Y (e t))`
     >- (Q.UNABBREV_TAC `e` >> ASM_SIMP_TAC std_ss []) \\
     DISCH_TAC \\
     MATCH_MP_TAC WG8_backward \\
     Q.EXISTS_TAC `Y` >> art [])
 (* Part III, c.f. WG8_IMP_CONST *)
 >> fs [weakly_guarded_def, EVERY_MEM]
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

Theorem weakly_guarded_rec_rule :
    !Xs Y E. ~MEM Y Xs /\ DISJOINT (FV E) (set Xs) /\ DISJOINT (BV E) (set Xs)
         ==> weakly_guarded Xs (rec Y E)
Proof
    RW_TAC std_ss [weakly_guarded_def, BV_def]
 >- ASM_SET_TAC []
 >> RW_TAC list_ss [EVERY_MEM, CCS_Subst_def]
 >> `Y <> X` by METIS_TAC [] >> fs []
 >> Know `!t. CCS_Subst E t X = E`
 >- (GEN_TAC >> MATCH_MP_TAC (EQ_IMP_LR CCS_Subst_elim) \\
     ASM_SET_TAC [])
 >> Rewr' >> REWRITE_TAC [WG2]
QED

(* a collection of all (forward) rules of `weakly_guarded` *)
val weakly_guarded_rules = save_thm
  ("weakly_guarded_rules",
    LIST_CONJ [weakly_guarded_nil,
               weakly_guarded_var,
               weakly_guarded_prefix_rule,
               weakly_guarded_sum_rule,
               weakly_guarded_par_rule,
               weakly_guarded_restr_rule,
               weakly_guarded_relab_rule,
               weakly_guarded_rec_rule]);

(* a collection of all backward rules of `weakly_guarded` *)
val weakly_guarded_backward_rules = save_thm
  ("weakly_guarded_backward_rules",
    LIST_CONJ [weakly_guarded_prefix_rule,
               weakly_guarded_sum,
               weakly_guarded_par,
               weakly_guarded_restr,
               weakly_guarded_relab,
               weakly_guarded_rec]);

(* c.f. CONTEXT_WG_combin *)
Theorem weakly_guarded_combin :
    !Xs Es C. ALL_DISTINCT Xs /\ context Xs C /\
              EVERY (weakly_guarded Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
              weakly_guarded Xs (CCS_SUBST (fromList Xs Es) C)
Proof
    Suff `!Xs. ALL_DISTINCT Xs ==>
               !Es C. context Xs C ==>
                      EVERY (weakly_guarded Xs) Es /\ (LENGTH Es = LENGTH Xs) ==>
                      weakly_guarded Xs (CCS_SUBST (fromList Xs Es) C)`
 >- METIS_TAC []
 >> NTAC 3 STRIP_TAC (* up to `!C.` *)
 >> Induct_on `C` >> RW_TAC std_ss [CCS_SUBST_def] (* 10 subgoals *)
 (* goal 1 (of 10): easy *)
 >- REWRITE_TAC [weakly_guarded_nil]
 (* goal 2 (of 10): not easy *)
 >- (Know `FDOM (fromList Xs Es) = set Xs`
     >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap) \\
     fs [EVERY_MEM, MEM_EL] \\
     Know `(fromList Xs Es) ' (EL n Xs) = EL n Es`
     >- (MATCH_MP_TAC fromList_FAPPLY_EL >> art []) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> art [])
 (* goal 3 (of 10): not hard *)
 >- (Know `FDOM (fromList Xs Es) = set Xs`
     >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap) \\
     MATCH_MP_TAC weakly_guarded_var_rule >> art [])
 (* goal 4 (of 10): not hard *)
 >- (IMP_RES_TAC context_prefix \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_prefix_rule \\
     MATCH_MP_TAC weakly_guarded_imp_context >> art [])
 (* goal 5 (of 10): easy *)
 >- (IMP_RES_TAC context_sum \\
     Q.PAT_X_ASSUM `context Xs C'' ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_sum_rule >> art [])
 (* goal 6 (of 10): easy *)
 >- (IMP_RES_TAC context_par \\
     Q.PAT_X_ASSUM `context Xs C'' ==> _` MP_TAC \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_par_rule >> art [])
 (* goal 7 (of 10): easy *)
 >- (IMP_RES_TAC context_restr \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_restr_rule >> art [])
 (* goal 8 (of 10): easy *)
 >- (IMP_RES_TAC context_relab \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC weakly_guarded_relab_rule >> art [])
 (* goal 9 (of 10): hard, impossible *)
 >- (Know `FDOM (fromList Xs Es) = set Xs`
     >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap) \\
     IMP_RES_TAC context_rec \\
     Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss [] \\
     rename1 `MEM X Xs` \\
     Know `CCS_SUBST ((fromList Xs Es) \\ X) C' = C'`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
         ASM_SET_TAC [context_def]) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Es) C' = C'`
     >- (MATCH_MP_TAC CCS_SUBST_elim' \\
         ASM_SIMP_TAC std_ss [FDOM_fromList] \\
         fs [BV_def, context_def]) >> DISCH_THEN (fs o wrap) \\
     fs [BV_def, context_def])
 (* goal 10 (of 10): not easy *)
 >> Know `FDOM (fromList Xs Es) = set Xs`
 >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap)
 >> IMP_RES_TAC context_rec
 >> Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss []
 >> Know `CCS_SUBST (fromList Xs Es) C' = C'`
 >- (irule CCS_SUBST_elim >> fs [context_def])
 >> DISCH_THEN (fs o wrap)
 >> rename1 `~MEM Y Xs`
 >> MATCH_MP_TAC weakly_guarded_rec_rule >> art []
 >> fs [context_def]
QED

Theorem disjoint_imp_weakly_guarded :
    !Xs E. DISJOINT (FV E) (set Xs) /\
           DISJOINT (BV E) (set Xs) ==> weakly_guarded Xs E 
Proof
    RW_TAC std_ss [weakly_guarded_def, BV_def, EVERY_MEM]
 >> MATCH_MP_TAC WG_CONST
 >> RW_TAC std_ss [IS_CONST_def]
 >> `X NOTIN (FV E)` by ASM_SET_TAC []
 >> fs [CCS_Subst_elim]
QED

Theorem disjoint_imp_context :
    !Xs E. DISJOINT (FV E) (set Xs) /\
           DISJOINT (BV E) (set Xs) ==> context Xs E 
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC weakly_guarded_imp_context
 >> MATCH_MP_TAC disjoint_imp_weakly_guarded >> art []
QED

(* ========================================================================== *)
(*  Section IV: Unique Solution of Equations                                  *)
(* ========================================================================== *)

(* NOTE: each E in Es MUST contain free variables up to Xs *)
Definition CCS_equation_def :
    CCS_equation (Xs :'a list) (Es :('a, 'b) CCS list) <=>
        ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs) /\
        EVERY (\E. (FV E) SUBSET (set Xs)) Es
End

(* A solution Ps of the CCS equation (group) Es[Xs] up to R,
  `ALL_PROC Ps` is required in (all) unique-solution proofs.

  `EVERY (\E. DISJOINT (BV E) (set Xs)) Ps` is not necessary but makes proofs
   (much) easier.
 *)
Definition CCS_solution_def :
    CCS_solution Xs Es R Ps <=>
        ALL_PROC Ps /\ 
        EVERY (\E. DISJOINT (BV E) (set Xs)) Ps /\
        LIST_REL R Ps (MAP (CCS_SUBST (fromList Xs Ps)) Es)
End

(* Each solution contains the same number of CCS processes as the
   variables - this is derived from LIST_REL's properties *)
Theorem CCS_solution_length :
    !Xs Es R Ps. CCS_equation Xs Es /\ CCS_solution Xs Es R Ps ==>
                 (LENGTH Ps = LENGTH Xs)
Proof
    RW_TAC list_ss [CCS_equation_def, CCS_solution_def]
 >> IMP_RES_TAC LIST_REL_LENGTH
 >> fs [LENGTH_MAP]
QED

(* Lemma 4.13 of [1] (the full version):

  "If the variable X is weakly guarded in E, and E{Ps/Xs} --u-> P',
   then P' takes the form E'{Ps/Xs} (for some context E'), and
   moreover, for any Qs, E{Qs/Xs} --u-> E'{Qs/Xs}."

   This lemma is used in proving both "strong_unique_solution"
   and "unique_solution_of_rooted_contractions" theorems.

   NOTE: `ALL_PROC Ps` is not required here.
   NOTE: `FV E SUBSET (set Xs)` and `FV E' SUBSET (set Xs)` were added
 *)
Theorem strong_unique_solution_lemma :
    !Xs E. weakly_guarded Xs E /\ FV E SUBSET (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==>
                !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
                       ?E'. context Xs E' /\ FV E' SUBSET (set Xs) /\
                            (P' = CCS_SUBST (fromList Xs Ps) E') /\
                            !Qs. (LENGTH Qs = LENGTH Xs) ==>
                                 TRANS (CCS_SUBST (fromList Xs Qs) E) u
                                       (CCS_SUBST (fromList Xs Qs) E')
Proof
    Q.X_GEN_TAC `Xs`
 >> Induct_on `E` >> rpt STRIP_TAC (* 8 subgoals *)
 (* Case 0: E = nil, impossible *)
 >- fs [CCS_SUBST_def, NIL_NO_TRANS]
 (* Case 1: E = Y, a variable, still impossible *)
 >- (rename1 `weakly_guarded Xs (var Y)` \\
     IMP_RES_TAC weakly_guarded_var \\
    `Y NOTIN (FDOM (fromList Xs Ps))` by METIS_TAC [FDOM_fromList] \\
     fs [CCS_SUBST_def, VAR_NO_TRANS])
 (* Case 2: E = b.E' *)
 >- (rename1 `weakly_guarded Xs (prefix b E)` \\
     fs [CCS_SUBST_def, TRANS_PREFIX_EQ, FV_def] \\
     Q.EXISTS_TAC `E` >> art [] \\
     IMP_RES_TAC weakly_guarded_prefix)
 (* Case 3: E = E1 + E2 *)
 >- (IMP_RES_TAC weakly_guarded_sum \\
     fs [CCS_SUBST_def, TRANS_SUM_EQ, FV_def] \\ (* 2 subgoals, same tactics *)
     RES_TAC >> fs [FV_def] >> Q.EXISTS_TAC `E''` >> fs [])
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
         K_TAC >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E1'`])) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `E' || E2` \\
       CONJ_TAC (* context Xs (E' || E2) *)
       >- (MATCH_MP_TAC context_par_rule >> art [] \\
           MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       CONJ_TAC >- ASM_SET_TAC [FV_def] \\ 
       ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E'` >> REWRITE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         K_TAC \\
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E1'`])) >> RW_TAC std_ss [] \\
       rename1 `context Xs E''` \\ (* fixes for stdknl *)
       Q.EXISTS_TAC `E1 || E''` \\
       CONJ_TAC (* context Xs (E1 || E'') *)
       >- (MATCH_MP_TAC context_par_rule >> art [] \\
           MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       CONJ_TAC >- ASM_SET_TAC [FV_def] \\ 
       ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ2_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E''` >> REWRITE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E1) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`label l`, `E1'`])) \\
       RW_TAC std_ss [] \\       
       Q.PAT_X_ASSUM
         `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E2) u P' ==> _`
         (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`label (COMPL l)`, `E2'`])) \\
       RW_TAC std_ss [] \\
       Q.EXISTS_TAC `E' || E''` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art []) \\
       CONJ_TAC >- ASM_SET_TAC [FV_def] \\ 
       ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
       GEN_TAC >> DISCH_TAC >> NTAC 2 DISJ2_TAC \\
       take [`CCS_SUBST (fromList Xs Qs) E'`,
             `CCS_SUBST (fromList Xs Qs) E''`, `l`] >> fs [] ])
 (* Case 5: E = restr f E' *)
 >- (IMP_RES_TAC weakly_guarded_restr \\
     fs [CCS_SUBST_def, TRANS_RESTR_EQ, FV_def] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!Ps. (LENGTH Ps = LENGTH Xs) ==> _` (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`tau`, `E''`])) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `restr f E'` \\
       rfs [CCS_SUBST_def, FV_def] \\
       MATCH_MP_TAC context_restr_rule >> art [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!Ps. (LENGTH Ps = LENGTH Xs) ==> _` (MP_TAC o (Q.SPEC `Ps`)) \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`label l`, `E''`])) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `restr f E'` \\
       rfs [CCS_SUBST_def, FV_def] \\
       MATCH_MP_TAC context_restr_rule >> art [] ])
 (* Case 6: E = relab E' R *)
 >- (IMP_RES_TAC weakly_guarded_relab \\
     Q.PAT_X_ASSUM `weakly_guarded Xs E /\ _ ==> _` MP_TAC \\
     fs [FV_def] >> rpt STRIP_TAC \\
     POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
     fs [CCS_SUBST_def, TRANS_RELAB_EQ] \\
     POP_ASSUM (MP_TAC o (Q.SPECL [`u'`, `E''`])) >> RW_TAC std_ss [] \\
     Q.EXISTS_TAC `relab E' R` \\
     CONJ_TAC >- (MATCH_MP_TAC context_relab_rule >> art []) \\
     ASM_SIMP_TAC std_ss [CCS_SUBST_def, FV_def] \\
     GEN_TAC >> DISCH_TAC \\
     take [`u'`, `CCS_SUBST (fromList Xs Qs) E'`] >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* Case 7 (difficult): E = rec Y E' *)
 >> rename1 `weakly_guarded Xs (rec Y E)`
 >> IMP_RES_TAC weakly_guarded_rec
 >> `DISJOINT (FV (rec Y E)) (set Xs)` by ASM_SET_TAC [FV_def]
 >> `DISJOINT (BV (rec Y E)) (set Xs)` by PROVE_TAC [weakly_guarded_def]
 (* simplify `CCS_Subst (rec Y E) (Ps |-> Qs)` *)
 >> Know `CCS_SUBST (fromList Xs Ps) (rec Y E) = rec Y E`
 >- (irule CCS_SUBST_elim >> art [])
 >> DISCH_THEN (fs o wrap)
 (* KEY step: let E' = P' *)
 >> Q.EXISTS_TAC `P'`
 >> Know `DISJOINT (FV P') (set Xs)`
 >- (MATCH_MP_TAC SUBSET_DISJOINT \\
     take [`FV (rec Y E) UNION BV (rec Y E)`, `set Xs`] >> art [SUBSET_REFL] \\
     CONJ_TAC >- ASM_SET_TAC [] \\
     MATCH_MP_TAC TRANS_FV_old \\
     Q.EXISTS_TAC `u` >> art []) >> DISCH_TAC
 >> Know `DISJOINT (BV P') (set Xs)`
 >- (MATCH_MP_TAC SUBSET_DISJOINT \\
     take [`BV (rec Y E)`, `set Xs`] >> art [SUBSET_REFL] \\
     MATCH_MP_TAC TRANS_BV \\
     Q.EXISTS_TAC `u` >> art []) >> DISCH_TAC
 >> CONJ_TAC (* context Xs P' *)
 >- (RW_TAC std_ss [context_def, EVERY_MEM] \\
     Suff `!t. CCS_Subst P' t X = P'`
     >- (Rewr' >> REWRITE_TAC [CONTEXT2]) \\
     REWRITE_TAC [GSYM CCS_Subst_elim] \\
     ASM_SET_TAC [])
 >> CONJ_TAC (* FV P' SUBSET set Xs *)
 >- (`FV P' SUBSET FV (rec Y E)`
        by PROVE_TAC [TRANS_FV] (* TRANS_FV_old is not enough! *) \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `FV (rec Y E)` >> art []) (* Yeah! *)
 >> CONJ_TAC (* P' = CCS_SUBST (Xs |-> Ps) P' *)
 >- (MATCH_MP_TAC EQ_SYM >> irule CCS_SUBST_elim >> art [])
 >> rpt STRIP_TAC
 >> Know `CCS_SUBST (fromList Xs Qs) (rec Y E) = rec Y E`
 >- (irule CCS_SUBST_elim >> art []) >> Rewr'
 >> Know `CCS_SUBST (fromList Xs Qs) P' = P'`
 >- (irule CCS_SUBST_elim >> art []) >> Rewr' >> art []
QED

(* THE STAGE THEOREM (failed attempt):
   Let the expression Es contain at most Xs, and let Xs be weakly guarded in Es,
   then:
        If Ps ~ E{Ps/Xs} and Qs ~ E{Qs/Xs} then Ps ~ Qs.

Theorem strong_unique_solution :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es STRONG_EQUIV) /\
                Qs IN (CCS_solution Xs Es STRONG_EQUIV) ==> STRONG_EQUIV Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
 >> Q.ABBREV_TAC `P = EL n Ps`
 >> Q.ABBREV_TAC `Q = EL n Qs`
 >> irule (REWRITE_RULE [RSUBSET] STRONG_BISIM_UPTO_THM)
 (* `FV G SUBSET (set Xs)` is necessary in the case of `par` *)
 >> Q.EXISTS_TAC `\x y. (x = y) \/
                        (?G. context Xs G /\ (FV G) SUBSET (set Xs) /\
                             (x = CCS_SUBST (fromList Xs Ps) G) /\
                             (y = CCS_SUBST (fromList Xs Qs) G))`
 >> BETA_TAC >> Reverse CONJ_TAC
 >- (DISJ2_TAC >> Q.EXISTS_TAC `var (EL n Xs)` \\
     unset [`P`, `Q`] \\
     SRW_TAC [] [CCS_SUBST_def, FV_def, MEM_EL, FDOM_fromList] (* 5 subgoals *)
     >- REWRITE_TAC [context_var]
     >- (Q.EXISTS_TAC `n` >> art [])
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >- METIS_TAC []
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >> METIS_TAC [])
 >> REWRITE_TAC [STRONG_BISIM_UPTO]
 >> fix [`P'`, `Q'`]
 >> BETA_TAC >> STRIP_TAC (* 2 subgoals here *)
 >- (POP_ASSUM MP_TAC >> RW_TAC std_ss [] >| (* 2 subgoals here *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `E1` >> art [O_DEF] \\
       Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
       BETA_TAC >> DISJ1_TAC >> REWRITE_TAC [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `E2` >> art [O_DEF] \\
       Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
       BETA_TAC >> DISJ1_TAC >> REWRITE_TAC [] ])
 (* `P'` and `Q'` are disappeared now: *)
 >> NTAC 2 POP_ORW
 >> NTAC 2 (POP_ASSUM MP_TAC) (* including `FV G SUBSET set Xs` *)
 >> Q.SPEC_TAC (`G`, `G`)
 >> Induct_on `G` (* 8 subgoals *)
 (* Case 0: E = nil, impossible *)
 >- RW_TAC std_ss [CCS_SUBST_def, FV_def, NIL_NO_TRANS]
 (* Case 1: E = var Y *)
 >- (Q.X_GEN_TAC `Y` >> NTAC 2 STRIP_TAC \\
     Reverse (Cases_on `Y IN set Xs`)
     >- (`DISJOINT (FV (var Y)) (set Xs)` by ASM_SET_TAC [FV_def] \\
         `DISJOINT (BV (var Y)) (set Xs)` by ASM_SET_TAC [BV_def] \\
         `(CCS_SUBST (fromList Xs Ps) (var Y) = var Y) /\
          (CCS_SUBST (fromList Xs Qs) (var Y) = var Y)`
             by METIS_TAC [CCS_SUBST_elim] \\
          RW_TAC std_ss [VAR_NO_TRANS]) \\
     fs [MEM_EL] >> rename1 `i < LENGTH Xs` \\
     Know `!Zs. (LENGTH Zs = LENGTH Xs) ==>
                (CCS_SUBST (fromList Xs Zs) (var (EL i Xs)) = EL i Zs)`
     >- (RW_TAC std_ss [CCS_SUBST_def, fromList_FAPPLY_EL, FDOM_fromList] \\
         METIS_TAC [MEM_EL]) >> DISCH_TAC \\
    `(CCS_SUBST (fromList Xs Ps) (var (EL i Xs)) = EL i Ps) /\
     (CCS_SUBST (fromList Xs Qs) (var (EL i Xs)) = EL i Qs)` by PROVE_TAC [] \\
  (* applying strong_unique_solution_lemma *)
     RW_TAC std_ss [FV_def] >| (* 2 subgoals (symmetric) *)
     [ (* goal 1 (of 2) *)
      `STRONG_EQUIV (EL i Ps) (CCS_SUBST (fromList Xs Ps) (EL i Es))`
         by METIS_TAC [EL_MAP] \\
       IMP_RES_TAC PROPERTY_STAR_LEFT \\
      `weakly_guarded Xs (EL i Es)` by PROVE_TAC [] \\
       Q.ABBREV_TAC `E = EL i Es` \\
      `?E'. context Xs E' /\ FV E' SUBSET (set Xs) /\
            (E2 = CCS_SUBST (fromList Xs Ps) E') /\
            !Qs. (LENGTH Qs = LENGTH Xs) ==>
                 TRANS (CCS_SUBST (fromList Xs Qs) E) u
                       (CCS_SUBST (fromList Xs Qs) E')`
         by METIS_TAC [Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) >> RW_TAC std_ss [] \\
      `STRONG_EQUIV (EL i Qs) (CCS_SUBST (fromList Xs Qs) E)`
         by METIS_TAC [EL_MAP] \\
      `?E2. TRANS (EL i Qs) u E2 /\
            STRONG_EQUIV (CCS_SUBST (fromList Xs Qs) E') E2`
         by METIS_TAC [PROPERTY_STAR_RIGHT, STRONG_EQUIV_SYM] \\
       Q.EXISTS_TAC `E2` >> RW_TAC std_ss [O_DEF] \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E'` >> art [] \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) E'` >> art [] \\
       DISJ2_TAC >> Q.EXISTS_TAC `E'` >> art [],
       (* goal 2 (of 2) *)
      `STRONG_EQUIV (EL i Qs) (CCS_SUBST (fromList Xs Qs) (EL i Es))`
         by METIS_TAC [EL_MAP] \\
      `weakly_guarded Xs (EL i Es)` by PROVE_TAC [] \\
       Q.ABBREV_TAC `E = EL i Es` \\
      `?E2'. TRANS (CCS_SUBST (fromList Xs Qs) E) u E2' /\ STRONG_EQUIV E2' E2`
          by METIS_TAC [PROPERTY_STAR_LEFT, STRONG_EQUIV_SYM] \\
      `weakly_guarded Xs E` by PROVE_TAC [] \\
      `?E'. context Xs E' /\ FV E' SUBSET (set Xs) /\
            (E2' = CCS_SUBST (fromList Xs Qs) E') /\
            !Ps. (LENGTH Ps = LENGTH Xs) ==>
                 TRANS (CCS_SUBST (fromList Xs Ps) E) u
                       (CCS_SUBST (fromList Xs Ps) E')`
         by METIS_TAC [Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
      `STRONG_EQUIV (EL i Ps) (CCS_SUBST (fromList Xs Ps) E)`
         by METIS_TAC [EL_MAP] \\
      `?E1. TRANS (EL i Ps) u E1 /\
            STRONG_EQUIV E1 (CCS_SUBST (fromList Xs Ps) E')`
         by METIS_TAC [PROPERTY_STAR_RIGHT] \\
       Q.EXISTS_TAC `E1` >> RW_TAC std_ss [O_DEF] \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E'` >> art [] \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) E'` >> art [] \\
       DISJ2_TAC >> Q.EXISTS_TAC `E'` >> art [] ])
 (* Case 2: E = prefix u G (not easy) *)
 >- (RW_TAC std_ss [FV_def, context_prefix_rewrite, CCS_SUBST_prefix,
                    TRANS_PREFIX_EQ] \\
     Q.PAT_X_ASSUM `context Xs G ==> _` MP_TAC >> RW_TAC bool_ss [] \\
     RW_TAC std_ss [O_DEF] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G` >> rw [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G` >> rw [STRONG_EQUIV_REFL] \\
     DISJ2_TAC >> Q.EXISTS_TAC `G` >> rw [])
(* Case 3: E = G + G' (not hard) *)
 >- (DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [context_sum_rewrite])) \\
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [FV_def])) \\
    `FV G SUBSET (set Xs) /\ FV G' SUBSET (set Xs)` by ASM_SET_TAC [] \\
     RW_TAC std_ss [CCS_SUBST_def, TRANS_SUM_EQ] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Q.PAT_X_ASSUM `context Xs G' ==> _` K_TAC \\
       Q.PAT_X_ASSUM `context Xs G  ==> _` MP_TAC >> RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `u`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) u E2 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E1`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E2` \\
         CONJ_TAC >- (DISJ1_TAC >> art []) \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E2` \\
         CONJ_TAC >- (DISJ1_TAC >> art []) \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ],
       (* goal 2 (of 4) *)
       Q.PAT_X_ASSUM `context Xs G  ==> _` K_TAC \\
       Q.PAT_X_ASSUM `context Xs G' ==> _` MP_TAC >> RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `u`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G') u E2 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E1`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `E2` \\
         CONJ_TAC >- (DISJ2_TAC >> art []) \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `E2` \\
         CONJ_TAC >- (DISJ2_TAC >> art []) \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ],
       (* goal 3 (of 4) *)
       Q.PAT_X_ASSUM `context Xs G' ==> _` K_TAC \\
       Q.PAT_X_ASSUM `context Xs G  ==> _` MP_TAC >> RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `u`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E2`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 3.1 (of 2) *)
         Q.EXISTS_TAC `E1` \\
         CONJ_TAC >- (DISJ1_TAC >> art []) \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [],
         (* goal 3.2 (of 2) *)
         Q.EXISTS_TAC `E1` \\
         CONJ_TAC >- (DISJ1_TAC >> art []) \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ],
       (* goal 4 (of 4) *)
       Q.PAT_X_ASSUM `context Xs G  ==> _` K_TAC \\
       Q.PAT_X_ASSUM `context Xs G' ==> _` MP_TAC >> RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `u`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G') u E1 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E2`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E1` \\
         CONJ_TAC >- (DISJ2_TAC >> art []) \\
         Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
         Q.EXISTS_TAC `E2` >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E1` \\
         CONJ_TAC >- (DISJ2_TAC >> art []) \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) G''` >> art [] \\
         Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) G''` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `G''` >> art [] ] ])
 (* Case 4: E = G || G' (hard) *)
 >- (DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [context_par_rewrite])) \\
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [FV_def])) \\
    `FV G SUBSET (set Xs) /\ FV G' SUBSET (set Xs)` by ASM_SET_TAC [] \\
     RW_TAC std_ss [CCS_SUBST_def, TRANS_PAR_EQ] >| (* 6 subgoals! *)
     [ (* goal 1 (of 6) *)
       Q.PAT_X_ASSUM `context Xs G' ==> _` K_TAC \\
       Q.PAT_X_ASSUM `context Xs G  ==> _` MP_TAC >> RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `u`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) u E2 ==> _` K_TAC \\
       Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _`
          (MP_TAC o (Q.SPEC `E1'`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `E2 || (CCS_SUBST (fromList Xs Qs) G')` \\
         CONJ_TAC >- (DISJ1_TAC >> Q.EXISTS_TAC `E2` >> art []) \\
         Q.EXISTS_TAC `E2 || CCS_SUBST (Xs |-> Qs) G'` \\
         REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (E1' || (CCS_SUBST (fromList Xs Ps) G'))
                      (E2  || (CCS_SUBST (fromList Xs Ps) G'))`
            by PROVE_TAC [STRONG_EQUIV_SUBST_PAR_R] \\
         Q.EXISTS_TAC `E2 || (CCS_SUBST (fromList Xs Ps) G')` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `E2 || G'` \\
         TODO (* possible *),
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E2 || (CCS_SUBST (fromList Xs Qs) G')` \\
         CONJ_TAC >- (DISJ1_TAC >> Q.EXISTS_TAC `E2` >> art []) \\
         Q.EXISTS_TAC `E2 || (CCS_SUBST (fromList Xs Qs) G')` \\
         REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV (E1' || (CCS_SUBST (fromList Xs Ps) G'))
                      (par (CCS_SUBST (fromList Xs Ps) G'')
                           (CCS_SUBST (fromList Xs Ps) G'))`
            by PROVE_TAC [STRONG_EQUIV_SUBST_PAR_R] \\
         Q.EXISTS_TAC `par (CCS_SUBST (fromList Xs Ps) G'')
                           (CCS_SUBST (fromList Xs Ps) G')` >> art [] \\
         DISJ2_TAC \\
         Q.EXISTS_TAC `G'' || G'` >> REWRITE_TAC [CCS_SUBST_par] \\
         CONJ_TAC >- art [context_par_rewrite] \\
         CONJ_TAC >- (REWRITE_TAC [FV_def] >> ASM_SET_TAC []) \\
         DIE (* impossible unless ... *) ],
       (* goal 2 (of 6) *)
       TODO,
       (* goal 3 (of 6) *)
       TODO,
       (* goal 4 (of 6) *)
       TODO,
       (* goal 5 (of 6) *)
       TODO,
       (* goal 6 (of 6) *)
       TODO ])
 (* Case 5: E = restr f G (not easy) *)
 >- (GEN_TAC \\
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [context_restr_rewrite])) \\
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [FV_def])) \\
     Q.PAT_X_ASSUM `context Xs G ==> _` MP_TAC \\
     RW_TAC std_ss [CCS_SUBST_restr, TRANS_RESTR_EQ] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `tau`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) tau E2 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `restr f E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
         Q.EXISTS_TAC `restr f E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr f E'') (restr f E2)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f E2` >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `restr f E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
        `STRONG_EQUIV (restr f (CCS_SUBST (fromList Xs Qs) G')) (restr f E2)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Qs) G')` >> art [] \\
        `STRONG_EQUIV (restr f E'') (restr f (CCS_SUBST (fromList Xs Ps) G'))`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Ps) G')` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr f G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         ASM_REWRITE_TAC [FV_def, CCS_SUBST_restr] ],
       (* goal 2 (of 4) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `label l`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM
         `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) (label l) E2 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `restr f E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
         Q.EXISTS_TAC `restr f E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr f E'') (restr f E2)` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f E2` >> art [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `restr f E2` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
        `STRONG_EQUIV (restr f (CCS_SUBST (fromList Xs Qs) G')) (restr f E2)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Qs) G')` >> art [] \\
        `STRONG_EQUIV (restr f E'') (restr f (CCS_SUBST (fromList Xs Ps) G'))`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Ps) G')` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr f G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         ASM_REWRITE_TAC [FV_def, CCS_SUBST_restr] ],
       (* goal 3 (of 4) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `tau`)) >>  RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) tau E1 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `restr f E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
         Q.EXISTS_TAC `restr f E''` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr f E1) (restr f E'')` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f E''` >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `restr f E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
        `STRONG_EQUIV (restr f (CCS_SUBST (fromList Xs Qs) G')) (restr f E'')`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Qs) G')` >> art [] \\
        `STRONG_EQUIV (restr f E1) (restr f (CCS_SUBST (fromList Xs Ps) G'))`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Ps) G')` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr f G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         ASM_REWRITE_TAC [FV_def, CCS_SUBST_restr] ],
       (* goal 4 (of 4) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `label l`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM
          `!E2. TRANS (CCS_SUBST (fromList Xs Ps) G) (label l) E2 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `restr f E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
         Q.EXISTS_TAC `restr f E''` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (restr f E1) (restr f E'')` by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f E''` >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `restr f E1` \\
         CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
        `STRONG_EQUIV (restr f (CCS_SUBST (fromList Xs Qs) G')) (restr f E'')`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Qs) G')` >> art [] \\
        `STRONG_EQUIV (restr f E1) (restr f (CCS_SUBST (fromList Xs Ps) G'))`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RESTR] \\
         Q.EXISTS_TAC `restr f (CCS_SUBST (fromList Xs Ps) G')` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `restr f G'` \\
         CONJ_TAC >- (MATCH_MP_TAC context_restr_rule >> art []) \\
         ASM_REWRITE_TAC [FV_def, CCS_SUBST_restr] ] ])
 (* Case 6: E = relab f G (not hard) *)
 >- (Q.X_GEN_TAC `rf` \\
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [context_relab_rewrite])) \\
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [FV_def])) \\
     Q.PAT_X_ASSUM `context Xs G ==> _` MP_TAC \\
     RW_TAC std_ss [CCS_SUBST_relab, TRANS_RELAB_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `u'`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM
         `!E2. TRANS (CCS_SUBST (fromList Xs Qs) G) u' E2 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 1.1 (of 2) *)
         Q.EXISTS_TAC `relab E2 rf` \\
         CONJ_TAC >- (take [`u'`, `E2`] >> art []) \\
         Q.EXISTS_TAC `relab E2 rf` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E'' E2` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (relab E'' rf) (relab E2 rf)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
         Q.EXISTS_TAC `relab E2 rf` >> art [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `relab E2 rf` \\
         CONJ_TAC >- (take [`u'`, `E2`] >> art []) \\
        `STRONG_EQUIV (relab (CCS_SUBST (fromList Xs Qs) G') rf) (relab E2 rf)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
         Q.EXISTS_TAC `relab (CCS_SUBST (fromList Xs Qs) G') rf` >> art [] \\
        `STRONG_EQUIV (relab E'' rf) (relab (CCS_SUBST (fromList Xs Ps) G') rf)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
         Q.EXISTS_TAC `relab (CCS_SUBST (fromList Xs Ps) G') rf` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `relab G' rf` \\
         CONJ_TAC >- (MATCH_MP_TAC context_relab_rule >> art []) \\
         ASM_REWRITE_TAC [FV_def, CCS_SUBST_relab] ],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!u. (!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u E1 ==> _) /\ _`
         (MP_TAC o (Q.SPEC `u'`)) >> RW_TAC bool_ss [] \\
       Q.PAT_X_ASSUM
         `!E1. TRANS (CCS_SUBST (fromList Xs Ps) G) u' E1 ==> _` K_TAC \\
       POP_ASSUM (MP_TAC o (Q.SPEC `E''`)) >> RW_TAC std_ss [O_DEF] >|
       [ (* goal 2.1 (of 2) *)
         Q.EXISTS_TAC `relab E1 rf` \\
         CONJ_TAC >- (take [`u'`, `E1`] >> art []) \\
         Q.EXISTS_TAC `relab E'' rf` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
        `STRONG_EQUIV E1 E''` by PROVE_TAC [STRONG_EQUIV_TRANS] \\
        `STRONG_EQUIV (relab E1 rf) (relab E'' rf)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
         Q.EXISTS_TAC `relab E'' rf` >> art [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `relab E1 rf` \\
         CONJ_TAC >- (take [`u'`, `E1`] >> art []) \\
        `STRONG_EQUIV (relab (CCS_SUBST (fromList Xs Qs) G') rf) (relab E'' rf)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
         Q.EXISTS_TAC `relab (CCS_SUBST (fromList Xs Qs) G') rf` >> art [] \\
        `STRONG_EQUIV (relab E1 rf) (relab (CCS_SUBST (fromList Xs Ps) G') rf)`
             by PROVE_TAC [STRONG_EQUIV_SUBST_RELAB] \\
         Q.EXISTS_TAC `relab (CCS_SUBST (fromList Xs Ps) G') rf` >> art [] \\
         DISJ2_TAC >> Q.EXISTS_TAC `relab G' rf` \\
         CONJ_TAC >- (MATCH_MP_TAC context_relab_rule >> art []) \\
         ASM_REWRITE_TAC [FV_def, CCS_SUBST_relab] ] ])
 (* Case 7: E = rec Y G (done, `context Xs` is essential here) *)
 >> POP_ASSUM K_TAC (* IH is not used here, removed *)
 >> Q.X_GEN_TAC `Y` >> DISCH_TAC
 >> IMP_RES_TAC context_rec
 >> `DISJOINT (FV (rec Y G)) (set Xs)` by ASM_SET_TAC [FV_def]
 >> `DISJOINT (BV (rec Y G)) (set Xs)` by ASM_SET_TAC [context_def]
 >> `(CCS_SUBST (fromList Xs Ps) (rec Y G) = rec Y G) /\
     (CCS_SUBST (fromList Xs Qs) (rec Y G) = rec Y G)`
        by METIS_TAC [CCS_SUBST_elim] >> NTAC 2 POP_ORW
 >> rpt STRIP_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E1` >> art [O_DEF] \\
      Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
      BETA_TAC >> DISJ1_TAC >> REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2` >> art [O_DEF] \\
      Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
      BETA_TAC >> DISJ1_TAC >> REWRITE_TAC [] ]
QED
 *)

(* ========================================================================== *)
(*  Section V: Unique Solution of (Rooted) Contractions                       *)
(* ========================================================================== *)

(* Transitivity is a property of equivalence but OBS_contracts is PreOrder,
   thus this lemma doesn't derive from LIST_REL_equivalence.
 *)
Theorem OBS_contracts_trans :
    !(Ps :('a, 'b) CCS list) Qs Rs.
          LIST_REL OBS_contracts Ps Qs /\ LIST_REL OBS_contracts Qs Rs
      ==> LIST_REL OBS_contracts Ps Rs
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC LIST_REL_trans
 >> Q.EXISTS_TAC `Qs` >> RW_TAC std_ss []
 >> MATCH_MP_TAC OBS_contracts_TRANS
 >> Q.EXISTS_TAC `EL n Qs` >> art []
QED

(* USC unfolding lemmas for unique_solution_of_rooted_contractions_lemma
  "USC" := "Unique Solution of (Rooted) Contractions".

   Lemma 1,4 are directly used; Lemma 2,3 are further lemmas of Lemma 4.
*)
Theorem USC_unfolding_lemma1[local] :
    !Xs Es E C C' Ps.
           CCS_equation Xs Es /\ EVERY (context Xs) Es /\
           CCS_solution Xs Es OBS_contracts Ps /\ context Xs C /\
           (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) /\
           (C' = \n. CCS_SUBST (fromList Xs (FUNPOW E n (MAP var Xs))) C)
       ==> !n. OBS_contracts (CCS_SUBST (fromList Xs Ps) C)
                             (CCS_SUBST (fromList Xs Ps) (C' n))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs)` by PROVE_TAC [CCS_equation_def]
 (* re-define C' (and E) back to abbreviations *)
 >> Q.PAT_X_ASSUM `C' = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.PAT_X_ASSUM `E  = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.ABBREV_TAC  `E  = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 >> Q.X_GEN_TAC `n` >> BETA_TAC
 (* applying CCS_SUBST_nested *)
 >> MP_TAC (Q.SPECL [`Xs`, `Ps`, `FUNPOW E n (MAP var Xs)`, `C`] CCS_SUBST_nested)
 >> Know `!i. LENGTH (FUNPOW E i (MAP var Xs)) = LENGTH Xs`
 >- (Induct_on `i` >- rw [FUNPOW_0, LENGTH_MAP] \\
     REWRITE_TAC [FUNPOW_SUC] \\
     Q.ABBREV_TAC `E' = FUNPOW E i (MAP var Xs)` \\
     Q.UNABBREV_TAC `E` >> ASM_SIMP_TAC std_ss [LENGTH_MAP])
 >> DISCH_TAC
 >> `DISJOINT (BV C) (set Xs)` by PROVE_TAC [context_def]
 >> `ALL_DISTINCT Xs` by PROVE_TAC [CCS_equation_def]
 >> `LENGTH Ps = LENGTH Xs` by PROVE_TAC [CCS_solution_length]
 >> RW_TAC std_ss []
 >> POP_ASSUM K_TAC (* useless after rewriting *)
 (* applying OBS_contracts_subst_context *)
 >> irule OBS_contracts_subst_context >> art []
 >> fs [CCS_solution_def]
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct_on `n`
 >- (REWRITE_TAC [FUNPOW_0] \\
     Suff `MAP (CCS_SUBST (fromList Xs Ps)) (MAP var Xs) = Ps`
     >- (Rewr' >> RW_TAC list_ss [LIST_REL_EL_EQN, OBS_contracts_REFL]) \\
     MATCH_MP_TAC LIST_EQ \\
     STRONG_CONJ_TAC >- ASM_SIMP_TAC list_ss [LENGTH_MAP] >> Rewr' \\
     RW_TAC list_ss [EL_MAP, CCS_SUBST_def, FDOM_fromList,
                     fromList_FAPPLY_EL] \\
     METIS_TAC [MEM_EL])
 >> MATCH_MP_TAC OBS_contracts_trans
 >> Q.EXISTS_TAC `MAP (CCS_SUBST (fromList Xs Ps)) (FUNPOW E n (MAP var Xs))`
 >> ASM_REWRITE_TAC []
 >> POP_ASSUM K_TAC (* already used assumption *)
 >> RW_TAC list_ss [LIST_REL_EL_EQN, EL_MAP]
 >> rename1 `i < LENGTH Xs`
 (* stage work *)
 >> SIMP_TAC std_ss [FUNPOW_SUC_LEFT, o_DEF] (* FUNPOW_SUC doesn't work *)
 >> Suff `!n. FUNPOW E n (E (MAP var Xs)) =
              MAP (CCS_SUBST (fromList Xs (E (MAP var Xs))))
                  (FUNPOW E n (MAP var Xs))`
 >- (Rewr' >> RW_TAC list_ss [EL_MAP] \\
  (* applying CCS_SUBST_nested AGAIN *)
     MP_TAC (Q.SPECL [`Xs`, `Ps`,
                      `(E :('a, 'b) CCS list -> ('a, 'b) CCS list) (MAP var Xs)`,
                      `EL i (FUNPOW E n (MAP var Xs))`] CCS_SUBST_nested) \\
    `LENGTH (E (MAP var Xs)) = LENGTH Xs` by METIS_TAC [FUNPOW_1] \\
     Know `!n. EVERY (context Xs) (FUNPOW E n (MAP var Xs))`
     >- (Induct_on `n`
         >- (RW_TAC list_ss [EVERY_MEM, FUNPOW_0, EL_MAP, context_var, MEM_EL] \\
             fs [EL_MAP, context_var]) \\
         rw [FUNPOW_SUC] \\
         Q.ABBREV_TAC `E' = FUNPOW E n (MAP var Xs)` \\
         Q.UNABBREV_TAC `E` \\
         RW_TAC list_ss [EVERY_MEM, EL_MAP, MEM_MAP] \\
         MATCH_MP_TAC context_combin >> art [] \\
         CONJ_TAC >- fs [EVERY_MEM] \\
         Q.UNABBREV_TAC `E'` >> art []) \\
     DISCH_THEN (ASSUME_TAC o (Q.SPEC `n`)) \\
     Know `context Xs (EL i (FUNPOW E n (MAP var Xs)))`
     >- (fs [EVERY_MEM, MEM_EL] \\
         POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC `i` >> art []) >> DISCH_TAC \\
    `DISJOINT (BV (EL i (FUNPOW E n (MAP var Xs)))) (set Xs)`
        by PROVE_TAC [context_def] \\
     RW_TAC bool_ss [] \\
     POP_ASSUM K_TAC (* already used assumption *) \\
  (* applying OBS_contracts_subst_context AGAIN *)
     irule OBS_contracts_subst_context >> art [] \\
     Q.UNABBREV_TAC `E` >> fs [] \\
     Know `MAP (CCS_SUBST (fromList Xs (MAP var Xs))) Es = Es`
     >- (RW_TAC list_ss [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC CCS_SUBST_self >> art [] \\
        `MEM (EL x Es) Es` by PROVE_TAC [MEM_EL] \\
         fs [EVERY_MEM, context_def]) >> Rewr' >> art [])
 (* now the last difficult part! *)
 >> Induct_on `n`
 >- (REWRITE_TAC [FUNPOW_0] \\
     Q.ABBREV_TAC `EX = E (MAP var Xs)` \\
     RW_TAC list_ss [LIST_EQ_REWRITE, EL_MAP]
     >- (unset [`EX`, `E`] >> ASM_SIMP_TAC list_ss [LENGTH_MAP]) \\
    `x < LENGTH (MAP var Xs) /\ x < LENGTH Xs` by METIS_TAC [LENGTH_MAP] \\
    `LENGTH EX = LENGTH Xs` by METIS_TAC [LENGTH_MAP] \\
    `MEM (EL x Xs) Xs` by PROVE_TAC [MEM_EL] \\
     ASM_SIMP_TAC list_ss [EL_MAP, CCS_SUBST_def, FDOM_fromList,
                           fromList_FAPPLY_EL])
 >> REWRITE_TAC [FUNPOW_SUC] >> POP_ORW
 >> Q.ABBREV_TAC `E' = FUNPOW E n (MAP var Xs)`
 >> Q.UNABBREV_TAC `E` >> BETA_TAC
 >> RW_TAC list_ss [LIST_EQ_REWRITE, EL_MAP]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC CCS_SUBST_nested >> art [LENGTH_MAP]
 >> Reverse CONJ_TAC
 >- (`MEM (EL x Es) Es` by PROVE_TAC [MEM_EL] >> fs [EVERY_MEM, context_def])
 >> Q.UNABBREV_TAC `E'`
 >> Q.ABBREV_TAC `E  = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 (* the last goal by induction *)
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct_on `n`
 >- rw [FUNPOW_0, LENGTH_MAP]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `E' = FUNPOW E n (MAP var Xs)`
 >> Q.UNABBREV_TAC `E` >> rw [LENGTH_MAP]
QED

(* `ALL_PROC Ps` is added to handle the last difficulity;
   `EVERY (\E. DISJOINT (BV E) (set Xs)) Ps` makes proofs easier.
 *)
Theorem USC_unfolding_lemma2[local] :
    !Xs. ALL_DISTINCT Xs ==>
      !E. weakly_guarded Xs E ==>
        !Ps u P'. (LENGTH Ps = LENGTH Xs) /\ ALL_PROC Ps /\
                  EVERY (\e. DISJOINT (BV e) (set Xs)) Ps /\
                  TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
            ?C'. context Xs C' /\
                 (P' = CCS_SUBST (fromList Xs Ps) C') /\
                 !Qs. (LENGTH Qs = LENGTH Xs) ==>
                      TRANS (CCS_SUBST (fromList Xs Qs) E) u
                            (CCS_SUBST (fromList Xs Qs) C')
Proof
    NTAC 2 STRIP_TAC (* up to `!E` *)
 >> Induct_on `E` (* 8 subgoals *)
 >- RW_TAC std_ss [CCS_SUBST_nil, NIL_NO_TRANS]
 (* 7 subgoals left *)
 >- (GEN_TAC >> DISCH_TAC \\
     IMP_RES_TAC weakly_guarded_var \\
     RW_TAC std_ss [CCS_SUBST_var, FDOM_fromList, VAR_NO_TRANS] \\
     METIS_TAC [FDOM_fromList])
 (* 6 subgoals left *)
 >- (RW_TAC std_ss [CCS_SUBST_prefix, TRANS_PREFIX_EQ] \\
     IMP_RES_TAC weakly_guarded_prefix \\
     Q.EXISTS_TAC `E` >> RW_TAC std_ss [])
 (* 5 subgoals left *)
 >- (RW_TAC std_ss [CCS_SUBST_sum, weakly_guarded_sum_rewrite] \\
     IMP_RES_TAC TRANS_SUM >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u`, `P'`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `C'` >> RW_TAC std_ss [] \\
       MATCH_MP_TAC SUM1 \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E' ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u`, `P'`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `C'` >> RW_TAC std_ss [] \\
       MATCH_MP_TAC SUM2 \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 (* 4 subgoals left *)
 >- (RW_TAC std_ss [CCS_SUBST_par, weakly_guarded_par_rewrite] \\
     IMP_RES_TAC TRANS_PAR >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u`, `E1`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `par C' E'` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art [] \\
                    MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       RW_TAC std_ss [CCS_SUBST_par] \\
       MATCH_MP_TAC PAR1 \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 3) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E' ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u`, `E1`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `par E C'` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art [] \\
                    MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       RW_TAC std_ss [CCS_SUBST_par] \\
       MATCH_MP_TAC PAR2 \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E' ==> _` MP_TAC \\
       Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `label (COMPL l)`, `E2`])) \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `label l`, `E1`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `par C' C''` \\
       CONJ_TAC >- (MATCH_MP_TAC context_par_rule >> art []) \\
       RW_TAC std_ss [CCS_SUBST_par] \\
       MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` \\
       CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 (* 3 subgoals left *)
 >- (RW_TAC std_ss [CCS_SUBST_restr, weakly_guarded_restr_rewrite,
                    TRANS_RESTR_EQ, BV_def] >|
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `tau`, `E''`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `restr f C'` >> RW_TAC std_ss [CCS_SUBST_restr] \\
       MATCH_MP_TAC context_restr_rule >> art [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` MP_TAC \\
       RW_TAC bool_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `label l`, `E''`])) \\
       RW_TAC bool_ss [] \\
       Q.EXISTS_TAC `restr f C'` >> RW_TAC std_ss [CCS_SUBST_restr] \\
       MATCH_MP_TAC context_restr_rule >> art [] ])
 (* 2 subgoals left *)
 >- (RW_TAC std_ss [CCS_SUBST_relab, weakly_guarded_relab_rewrite,
                    TRANS_RELAB_EQ, BV_def] \\
     Q.PAT_X_ASSUM `weakly_guarded Xs E ==> _` MP_TAC \\
     RW_TAC bool_ss [] \\
     POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u'`, `E''`])) \\
     RW_TAC bool_ss [] \\
     Q.EXISTS_TAC `relab C' R` >> RW_TAC std_ss [CCS_SUBST_relab]
     >- (MATCH_MP_TAC context_relab_rule >> art []) \\
     Q.EXISTS_TAC `u'` >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* the last goal (hard) *)
 >> RW_TAC std_ss [CCS_SUBST_rec, BV_def]
 >> IMP_RES_TAC weakly_guarded_rec
 >> Know `FDOM (fromList Xs Ps) = set Xs`
 >- (MATCH_MP_TAC FDOM_fromList >> art [])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Q.EXISTS_TAC `P'`
 (* TODO: check if `DISJOINT (BV P') (set Xs)` can be eliminated,
    by eliminating it in all dependent lemmas. *)
 >> Suff `DISJOINT (FV P') (set Xs) /\ DISJOINT (BV P') (set Xs)`
 >- (STRIP_TAC \\
     CONJ_TAC >- (MATCH_MP_TAC disjoint_imp_context >> art []) \\
     CONJ_TAC >- (MATCH_MP_TAC EQ_SYM \\
                  irule CCS_SUBST_elim >> art []) \\
     RW_TAC std_ss [FDOM_fromList] \\
     Know `CCS_SUBST (fromList Xs Qs) P' = P'`
     >- (irule CCS_SUBST_elim >> art []) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Ps) E = E`
     >- (irule CCS_SUBST_elim >> fs [weakly_guarded_def]) \\
     DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap) \\
     Know `CCS_SUBST (fromList Xs Qs) E = E`
     >- (irule CCS_SUBST_elim >> fs [weakly_guarded_def]) \\
     DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap))
 (* cleanups and renames before the final battle *)
 >> rename1 `~MEM Y Xs`
 >> Q.PAT_X_ASSUM `!Ps u P'. LENGTH Ps = LENGTH Xs /\ _ ==> _` K_TAC
 (* hard left goal *)
 >> Q.ABBREV_TAC `P = CCS_SUBST (fromList Xs Ps) E`
 >> IMP_RES_TAC TRANS_FV
 >> IMP_RES_TAC TRANS_BV
 >> FULL_SIMP_TAC bool_ss [FV_def, BV_def]
 >> `DISJOINT (BV E) (set Xs)` by PROVE_TAC [weakly_guarded_def]
 (* applying CCS_SUBST_[FV|BV]_SUBSET *)
 >> Know `BV P SUBSET (BV E) UNION (BIGUNION (IMAGE BV (set Ps)))`
 >- (Q.UNABBREV_TAC `P` \\
     MATCH_MP_TAC BV_SUBSET_BIGUNION >> art []) >> DISCH_TAC
 >> Know `FV P SUBSET (FV E) UNION (BIGUNION (IMAGE FV (set Ps)))`
 >- (Q.UNABBREV_TAC `P` \\
     MATCH_MP_TAC FV_SUBSET_BIGUNION >> art []) >> DISCH_TAC
 >> FULL_SIMP_TAC bool_ss [ALL_PROC_def, EVERY_MEM, IS_PROC_def]
 (* more cleanups before the final magic *)
 >> NTAC 2 (Q.PAT_X_ASSUM `weakly_guarded _ _` K_TAC) (* used *)
 >> Q.PAT_X_ASSUM `TRANS (rec Y P) u P'`       K_TAC  (* useless *)
 >> Q.PAT_X_ASSUM `LENGTH Ps = LENGTH Xs`      K_TAC  (* useless *)
 >> CONJ_TAC (* DISJOINT (FV P') (set Xs) *)
 >- (Know `BIGUNION (IMAGE FV (set Ps)) = EMPTY`
     >- rw [NOT_IN_EMPTY, IN_BIGUNION_IMAGE, IMAGE_EQ_SING] \\
     ASM_SET_TAC [])
 >> Know `DISJOINT (BIGUNION (IMAGE BV (set Ps))) (set Xs)`
 >- (rw [DISJOINT_BIGUNION] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* the final magic *)
 >> ASM_SET_TAC []
QED

(* Needed by lemma3. It depends on lemma2 and repeated applications of
   the (celebrated) CCS_SUBST_nested.

  `EVERY (\e. DISJOINT (BV e) (set Xs)) Ps` comes from lemma2.
 *)
Theorem USC_unfolding_lemma3[local] :
    !Xs C Es. ALL_DISTINCT Xs /\ context Xs C /\ (LENGTH Es = LENGTH Xs) /\
              EVERY (weakly_guarded Xs) Es ==>
       !Ps x P'. (LENGTH Ps = LENGTH Xs) /\ ALL_PROC Ps /\
                 EVERY (\e. DISJOINT (BV e) (set Xs)) Ps /\
                 TRANS (CCS_SUBST
                         (fromList Xs
                           (MAP (CCS_SUBST (fromList Xs Ps)) Es)) C) x P' ==>
          ?C'. context Xs C' /\
               (P' = CCS_SUBST (fromList Xs Ps) C') /\
               !Qs. (LENGTH Qs = LENGTH Xs) ==>
                    TRANS (CCS_SUBST (fromList Xs
                                       (MAP (CCS_SUBST (fromList Xs Qs)) Es)) C) x
                          (CCS_SUBST (fromList Xs Qs) C')
Proof
    rpt STRIP_TAC
 (* `context Xs C` can be replaced with just this one. *)
 >> `DISJOINT (BV C) (set Xs)` by PROVE_TAC [context_def]
 >> Know `weakly_guarded Xs (CCS_SUBST (fromList Xs Es) C)`
 >- (MATCH_MP_TAC weakly_guarded_combin >> art []) >> DISCH_TAC
 (* applying CCS_SUBST_nested *)
 >> Know `CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Ps)) Es)) C =
          CCS_SUBST (fromList Xs Ps) (CCS_SUBST (fromList Xs Es) C)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC CCS_SUBST_nested >> art [])
 >> DISCH_THEN (fs o wrap)
 >> Q.ABBREV_TAC `C' = CCS_SUBST (fromList Xs Es) C`
 (* applying USC_unfolding_lemma2 *)
 >> MP_TAC (Q.SPEC `Xs` USC_unfolding_lemma2)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPEC `C'`)) >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `x`, `P'`]))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `C''` >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!Qs. LENGTH Qs = LENGTH Xs ==> _` (MP_TAC o (Q.SPEC `Qs`))
 >> RW_TAC std_ss []
 (* applying CCS_SUBST_nested AGAIN *)
 >> Suff `CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Qs)) Es)) C =
          CCS_SUBST (fromList Xs Qs) C'` >- rw []
 >> Q.UNABBREV_TAC `C'`
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC CCS_SUBST_nested >> art []
QED

(* (directly) used in unique_solution_of_rooted_contractions_lemma *)
Theorem USC_unfolding_lemma4[local] :
    !Xs Es E C C'.
        CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\ context Xs C /\
        (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) /\
        (C' = \n. CCS_SUBST (fromList Xs (FUNPOW E n (MAP var Xs))) C) ==>
        !n xs Ps P'.
           (LENGTH Ps = LENGTH Xs) /\ ALL_PROC Ps /\
           EVERY (\e. DISJOINT (BV e) (set Xs)) Ps /\
           TRACE (CCS_SUBST (fromList Xs Ps) (C' n)) xs P' /\ LENGTH xs <= n ==>
           ?C''. context Xs C'' /\ (P' = CCS_SUBST (fromList Xs Ps) C'') /\
                 !Qs. (LENGTH Qs = LENGTH Xs) ==>
                      TRACE (CCS_SUBST (fromList Xs Qs) (C' n)) xs
                            (CCS_SUBST (fromList Xs Qs) C'')
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs)`
       by PROVE_TAC [CCS_equation_def]
 >> `DISJOINT (BV C) (set Xs)` by PROVE_TAC [context_def]
 (* re-define C' and E back to abbreviations *)
 >> Q.PAT_X_ASSUM `C' = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.PAT_X_ASSUM `E  = _` ((FULL_SIMP_TAC pure_ss) o wrap)
 >> Q.ABBREV_TAC  `E  = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 >> Q.ABBREV_TAC  `C' = \n. CCS_SUBST (fromList Xs (FUNPOW E n (MAP var Xs))) C`
 >> Know `C' 0 = C`
 >- (Q.UNABBREV_TAC `C'` >> SIMP_TAC std_ss [FUNPOW_0] \\
     MATCH_MP_TAC CCS_SUBST_self \\
     PROVE_TAC [context_def, CCS_equation_def]) >> DISCH_TAC
 (* kick-start: induction *)
 >> Induct_on `n` >> rpt STRIP_TAC
 >- (fs [TRACE_NIL] >> rfs [] \\
     Q.EXISTS_TAC `C` >> art [])
 (* stage work *)
 >> Q.PAT_X_ASSUM `TRACE _ xs P'` MP_TAC
 >> Know `!i Qs. (LENGTH Qs = LENGTH Xs) ==>
                 CCS_SUBST (fromList Xs Qs) (C' (SUC i)) =
                 CCS_SUBST (fromList Xs (E Qs)) (C' i)`
 >- (Induct_on `i`
     >- (NTAC 2 STRIP_TAC \\
         ASM_SIMP_TAC arith_ss [] \\
         Q.UNABBREV_TAC `C'` >> SIMP_TAC std_ss [FUNPOW_1] \\
         Know `CCS_SUBST (fromList Xs Qs)
                 (CCS_SUBST (fromList Xs (E (MAP var Xs))) C) =
               CCS_SUBST (fromList Xs (MAP (CCS_SUBST (fromList Xs Qs))
                                           (E (MAP var Xs)))) C`
         >- (MATCH_MP_TAC CCS_SUBST_nested >> art [] \\
             Q.UNABBREV_TAC `E` >> rw [LENGTH_MAP ]) >> Rewr' \\
         Suff `MAP (CCS_SUBST (fromList Xs Qs)) (E (MAP var Xs)) = E Qs` >- rw [] \\
         Q.UNABBREV_TAC `E` >> BETA_TAC \\
         Suff `MAP (CCS_SUBST (fromList Xs (MAP var Xs))) Es = Es` >- rw [] \\
         RW_TAC list_ss [LIST_EQ_REWRITE, EL_MAP] \\
         MATCH_MP_TAC CCS_SUBST_self \\
         fs [CCS_equation_def, EVERY_MEM, weakly_guarded_def] \\
        `MEM (EL x Es) Es` by PROVE_TAC [MEM_EL] \\
         METIS_TAC []) \\
     NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM `C' 0 = C` K_TAC \\
     (* stage work *)
     Q.UNABBREV_TAC `C'` >> fs [FUNPOW_SUC] \\
     Q.ABBREV_TAC `E' = E (FUNPOW E i (MAP var Xs))` \\
     Know `CCS_SUBST (fromList Xs (E E')) C =
           CCS_SUBST (fromList Xs Es) (CCS_SUBST (fromList Xs E') C)`
     >- (ASM_SIMP_TAC std_ss [] \\
         cheat) >> Rewr' \\
     Q.ABBREV_TAC `E'' = CCS_SUBST (fromList Xs E') C` \\
     Q.UNABBREV_TAC `E` >> BETA_TAC \\
     MATCH_MP_TAC CCS_SUBST_nested >> art [] \\
     Q.UNABBREV_TAC `E''` >> fs [] \\
  (* applying BV_SUBSET_BIGUNION *)
     cheat)
 >> DISCH_TAC >> ASM_SIMP_TAC std_ss []
 >> DISCH_TAC
 >> Know `!Qs. (LENGTH Qs = LENGTH Xs) ==> (LENGTH (E Qs) = LENGTH Xs)`
 >- (rpt STRIP_TAC \\
     Q.UNABBREV_TAC `E` >> ASM_SIMP_TAC std_ss [LENGTH_MAP]) >> DISCH_TAC
 >> `LENGTH (E Ps) = LENGTH Xs` by PROVE_TAC []
 >> Know `ALL_PROC (E Ps)`
 >- (Q.UNABBREV_TAC `E` \\
     RW_TAC lset_ss [ALL_PROC_def, IS_PROC_def, EVERY_MEM, MEM_MAP, MEM_EL] \\
     rename1 `i < LENGTH Xs` \\
    `i < LENGTH Es` by PROVE_TAC [] \\
     ASM_SIMP_TAC lset_ss [EL_MAP] \\
     Q.ABBREV_TAC `E = EL i Es` \\
  (* FV (CCS_SUBST (Xs |-> Ps) E) = {}, given `ALL_PROC Ps` *)
     REWRITE_TAC [GSYM IS_PROC_def] \\
     MATCH_MP_TAC CCS_SUBST_IS_PROC >> art [] \\
     fs [CCS_equation_def, EVERY_MEM, weakly_guarded_def] \\
    `MEM E Es` by METIS_TAC [MEM_EL] \\
     PROVE_TAC []) >> DISCH_TAC
 >> Know `EVERY (\e. DISJOINT (BV e) (set Xs)) (E Ps)`
 >- (Q.UNABBREV_TAC `E` \\
     RW_TAC lset_ss [EVERY_MEM, MEM_MAP, MEM_EL] \\
     rename1 `i < LENGTH Xs` \\
    `i < LENGTH Es` by PROVE_TAC [] \\
     ASM_SIMP_TAC lset_ss [EL_MAP] \\
     Q.ABBREV_TAC `E = EL i Es` \\
     fs [ALL_PROC_def, EVERY_MEM, IS_PROC_def, weakly_guarded_def] \\
    `MEM E Es` by PROVE_TAC [MEM_EL] \\         
     Suff `(BV (CCS_SUBST (fromList Xs Ps) E)) SUBSET
           (BV E) UNION (BIGUNION (IMAGE BV (set Ps)))` >- ASM_SET_TAC [] \\
     MATCH_MP_TAC BV_SUBSET_BIGUNION >> METIS_TAC []) >> DISCH_TAC
 >> IMP_RES_TAC TRACE_cases2
 >> Cases_on `xs`
 >- (FULL_SIMP_TAC bool_ss [NULL] \\
    `LENGTH (epsilon :'b Action list) <= n` by FULL_SIMP_TAC arith_ss [LENGTH] \\
     Know `!Ys. (LENGTH Ys = LENGTH Xs) ==> (LENGTH (E Ys) = LENGTH Xs)`
     >- (rpt STRIP_TAC \\
         Q.UNABBREV_TAC `E` >> ASM_SIMP_TAC list_ss [LENGTH_MAP]) \\
     DISCH_TAC \\
     Q.PAT_X_ASSUM `!xs Ps P'. _ ==> _`
        (MP_TAC o (Q.SPECL [`[] :'b Action list`,
                            `(E :('a, 'b) CCS list -> ('a, 'b) CCS list) Ps`, `P'`])) \\
     Q.PAT_ASSUM `_ = P'` (ONCE_REWRITE_TAC o wrap) \\
     RW_TAC bool_ss [] \\
     Q.EXISTS_TAC `CCS_SUBST (fromList Xs Es) C''`  \\
     CONJ_TAC (* context Xs (CCS_SUBST (Xs |-> Es) C'') *)
     >- (MATCH_MP_TAC context_combin >> fs [EVERY_MEM] \\
         rpt STRIP_TAC >> MATCH_MP_TAC weakly_guarded_imp_context \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     CONJ_TAC (* CCS_SUBST_nested *)
     >- (Q.PAT_X_ASSUM `CCS_SUBST (fromList Xs (E Ps)) (C' n) = _`
            (ONCE_REWRITE_TAC o wrap) \\
         Q.UNABBREV_TAC `E` >> BETA_TAC \\
         MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC CCS_SUBST_nested \\
         fs [context_def]) \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM `!Qs. (LENGTH Qs = LENGTH Xs) ==> _`
        (MP_TAC o (Q.SPEC `(E :('a, 'b) CCS list -> ('a, 'b) CCS list) Qs`)) \\
     RW_TAC bool_ss [] \\
     Suff `CCS_SUBST (fromList Xs Qs) (CCS_SUBST (fromList Xs Es) C'') =
           CCS_SUBST (fromList Xs (E Qs)) C''` >- (Rewr' >> art []) \\
     POP_ASSUM K_TAC \\
     Q.UNABBREV_TAC `E` >> fs [] \\
     MATCH_MP_TAC CCS_SUBST_nested >> fs [context_def])
 (* hard part *)
 >> FULL_SIMP_TAC list_ss []
 >> `LENGTH (FRONT (h::t)) <= n` by PROVE_TAC [LENGTH_FRONT_CONS]
 >> rename1 `TRANS P _ P'`
 >> Q.ABBREV_TAC `us = FRONT (h::t)`
 >> Q.ABBREV_TAC `u = LAST (h::t)`
 >> Q.PAT_X_ASSUM `!us Ps P'. _ ==> ?C''. _`
      (MP_TAC o
       (Q.SPECL [`us`, `(E :('a, 'b) CCS list -> ('a, 'b) CCS list) Ps`, `P`]))
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`Xs`, `C''`, `Es`] USC_unfolding_lemma3) (* here *)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`Ps`, `u`, `P'`]))
 >> RW_TAC bool_ss []
 >> Q.EXISTS_TAC `C'''` >> art []
 >> RW_TAC std_ss [Once TRACE_cases2, NULL]
 >> Q.PAT_X_ASSUM `!Qs. (LENGTH Qs = LENGTH Xs) ==> _` (MP_TAC o (Q.SPEC `Qs`))
 >> RW_TAC bool_ss []
 >> Q.EXISTS_TAC `CCS_SUBST (fromList Xs (E Qs)) C''`
 >> `LENGTH (E Qs) = LENGTH Xs` by PROVE_TAC []
 >> ASM_SIMP_TAC std_ss []
QED

(* Lemma 3.9 of [2], the full (multivariate) version *)
Theorem unique_solution_of_rooted_contractions_lemma :
    !Xs Es Ps Qs. CCS_equation Xs Es /\
                  EVERY (weakly_guarded Xs) Es /\
                  CCS_solution Xs Es OBS_contracts Ps /\
                  CCS_solution Xs Es OBS_contracts Qs ==>
        !C. context Xs C ==>
            (!l R. WEAK_TRANS (CCS_SUBST (fromList Xs Ps) C) (label l) R ==>
                   ?C'. context Xs C' /\
                        R contracts (CCS_SUBST (fromList Xs Ps) C') /\
                        (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y))
                          (CCS_SUBST (fromList Xs Qs) C)
                          (CCS_SUBST (fromList Xs Qs) C')) /\
            (!R. WEAK_TRANS (CCS_SUBST (fromList Xs Ps) C) tau R ==>
                 ?C'. context Xs C' /\
                      R contracts (CCS_SUBST (fromList Xs Ps) C') /\
                      (WEAK_EQUIV O EPS) (CCS_SUBST (fromList Xs Qs) C)
                                         (CCS_SUBST (fromList Xs Qs) C'))
Proof
    NTAC 7 STRIP_TAC (* up to `context Xs C` *)
 >> Know `EVERY (context Xs) Es`
 >- (fs [EVERY_MEM] >> rpt STRIP_TAC \\
     MATCH_MP_TAC weakly_guarded_imp_context \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC `E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es`
 >> Q.ABBREV_TAC `C' = \n. CCS_SUBST (fromList Xs (FUNPOW E n (MAP var Xs))) C`
 (* applying context_combin *)
 >> Know `!n. context Xs (C' n)`
 >- (GEN_TAC >> Q.UNABBREV_TAC `C'` >> BETA_TAC \\
     MATCH_MP_TAC context_combin >> fs [CCS_equation_def] \\
     Q.SPEC_TAC (`n`, `n`) \\
     Induct_on `n` >- (RW_TAC list_ss [FUNPOW_0, EVERY_MEM, MEM_MAP] \\
                       REWRITE_TAC [context_var]) \\
     REWRITE_TAC [FUNPOW_SUC] \\
     Q.ABBREV_TAC `Rs = FUNPOW E n (MAP var Xs)` \\
     Q.UNABBREV_TAC `E` >> BETA_TAC >> art [LENGTH_MAP] \\
     RW_TAC list_ss [EVERY_MEM, MEM_MAP] \\
     MATCH_MP_TAC context_combin >> fs [EVERY_MEM])
 >> DISCH_TAC
 >> Know `!n. OBS_contracts (CCS_SUBST (fromList Xs Ps) C)
                            (CCS_SUBST (fromList Xs Ps) (C' n))`
 >- (MATCH_MP_TAC USC_unfolding_lemma1 \\
     take [`Es`, `E`] >> unset [`E`, `C'`] >> art [])
 >> DISCH_TAC
 >> Know `!n. OBS_contracts (CCS_SUBST (fromList Xs Qs) C)
                            (CCS_SUBST (fromList Xs Qs) (C' n))`
 >- (MATCH_MP_TAC USC_unfolding_lemma1 \\
     take [`Es`, `E`] >> unset [`E`, `C'`] >> art [])
 >> DISCH_TAC
 >> `(LENGTH Ps = LENGTH Xs) /\ (LENGTH Qs = LENGTH Xs)`
      by PROVE_TAC [CCS_solution_length]
 >> fs [CCS_solution_def]
 >> rpt STRIP_TAC (* 2 subgoals (not symmetric!) *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [Action_distinct_label] \\
     `OBS_contracts (CCS_SUBST (fromList Xs Ps) C)
                    (CCS_SUBST (fromList Xs Ps) (C' (LENGTH us)))`
        by PROVE_TAC [] \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`us`, `l`, `R`]) o
                 (MATCH_MP OBS_contracts_AND_TRACE_label)) \\
      RW_TAC std_ss [] \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Know `?C''. context Xs C'' /\ (E2 = CCS_SUBST (fromList Xs Ps) C'') /\
                  !Qs. (LENGTH Qs = LENGTH Xs) ==>
                       TRACE (CCS_SUBST (fromList Xs Qs) (C' n)) xs'
                             (CCS_SUBST (fromList Xs Qs) C'')`
      >- (irule USC_unfolding_lemma4 >> art [] \\
          take [`C`, `E`, `Es`] >> unset [`E`, `C'`] >> art []) \\
      STRIP_TAC >> POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) \\
     `LENGTH Qs = LENGTH Xs` by PROVE_TAC [CCS_solution_length] \\
      RW_TAC std_ss [] \\
     `OBS_contracts (CCS_SUBST (fromList Xs Qs) C)
                    (CCS_SUBST (fromList Xs Qs) (C' n))` by PROVE_TAC [] \\
      Q.EXISTS_TAC `C''` >> art [] \\
      Know `WEAK_TRANS (CCS_SUBST (fromList Xs Qs) (C' n)) (label l)
                       (CCS_SUBST (fromList Xs Qs) C'')`
      >- (REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
          Q.EXISTS_TAC `xs'` >> art [] \\
          MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
          Q.EXISTS_TAC `label l` >> art []) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC OBS_contracts_WEAK_TRANS_label' \\
      Q.EXISTS_TAC `E1` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE >> fs [] \\
     `OBS_contracts (CCS_SUBST (fromList Xs Ps) C)
                    (CCS_SUBST (fromList Xs Ps) (C' (LENGTH us)))`
        by PROVE_TAC [] \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`us`, `R`]) o
                 (MATCH_MP OBS_contracts_AND_TRACE_tau)) \\
      RW_TAC std_ss [] \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Know `?C''. context Xs C'' /\ (E2 = CCS_SUBST (fromList Xs Ps) C'') /\
                  !Qs. (LENGTH Qs = LENGTH Xs) ==>
                       TRACE (CCS_SUBST (fromList Xs Qs) (C' n)) xs'
                             (CCS_SUBST (fromList Xs Qs) C'')`
      >- (irule USC_unfolding_lemma4 >> art [] \\
          take [`C`, `E`, `Es`] >> unset [`E`, `C'`] >> art []) \\
      STRIP_TAC >> POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) \\
     `LENGTH Qs = LENGTH Xs` by PROVE_TAC [CCS_solution_length] \\
      RW_TAC std_ss [] \\
     `OBS_contracts (CCS_SUBST (fromList Xs Qs) C)
                    (CCS_SUBST (fromList Xs Qs) (C' n))` by PROVE_TAC [] \\
      Q.EXISTS_TAC `C''` >> art [] \\
      Know `EPS (CCS_SUBST (fromList Xs Qs) (C' n))
                (CCS_SUBST (fromList Xs Qs) C'')`
      >- (REWRITE_TAC [EPS_AND_TRACE] \\
          Q.EXISTS_TAC `xs'` >> art []) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC OBS_contracts_EPS' \\
      Q.EXISTS_TAC `E1` >> art [] ]
QED

(* Shared lemma for unique_solution_of_obs_contractions and
   unique_solution_of_rooted_contractions. *)
val shared_lemma = Q.prove (
   `CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
    CCS_solution Xs Es OBS_contracts Ps /\
    CCS_solution Xs Es OBS_contracts Qs
   ==>
    WEAK_BISIM (\R S. ?C. context Xs C /\
                          WEAK_EQUIV R (CCS_SUBST (fromList Xs Ps) C) /\
                          WEAK_EQUIV S (CCS_SUBST (fromList Xs Qs) C))`,
 (* proof *)
    rpt STRIP_TAC >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 (* compatible with symbols in UniqueSolutionsTheory.shared_lemma *)
 >> rename1 `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
 >> rename1 `WEAK_EQUIV E'  (CCS_SUBST (fromList Xs Ps) C)`
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (fromList Xs Ps) C)`
        (MP_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RW_TAC std_ss [] \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Ps`, `Qs`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      POP_ASSUM K_TAC (* !R. EPS _ R ==> _ *) \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`l`, `E2`])) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
        (MP_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      Reverse CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
        (MP_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RW_TAC std_ss [] \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Qs`, `Ps`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      POP_ASSUM K_TAC (* !R. EPS _ R ==> _ *) \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`l`, `E2'`])) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\

      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (fromList Xs Ps) C)`
        (MP_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (from Xs Ps) C)`
        (MP_TAC o (Q.SPEC `E1`) o (MATCH_MP WEAK_EQUIV_TRANS_tau)) \\
      RW_TAC std_ss [] \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- (Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
          Q.EXISTS_TAC `C` >> art []) \\
      Q.PAT_X_ASSUM `EPS _ E2` K_TAC \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Ps`, `Qs`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS _ (label l) R => _` K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `E2`)) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (fromList Xs Qs) C)`
        (MP_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      Reverse CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (CCS_SUBST (from Xs Qs) C)`
        (MP_TAC o (Q.SPEC `E2`) o (MATCH_MP WEAK_EQUIV_TRANS_tau)) \\
      RW_TAC std_ss [] \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- (Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
          Q.EXISTS_TAC `C` >> art []) \\
      Q.PAT_X_ASSUM `EPS _ E2'` K_TAC \\
      MP_TAC (Q.SPECL [`Xs`, `Es`, `Qs`, `Ps`]
                      unique_solution_of_rooted_contractions_lemma) >> RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS _ (label l) R => _` K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `E2'`)) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (CCS_SUBST (fromList Xs Ps) C)`
        (MP_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]
QED

(* Theorem 3.10 of [2], full version *)
Theorem unique_solution_of_obs_contractions :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es OBS_contracts) /\
                Qs IN (CCS_solution Xs Es OBS_contracts) ==> WEAK_EQUIV Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. context Xs C /\
                            WEAK_EQUIV R (CCS_SUBST (fromList Xs Ps) C) /\
                            WEAK_EQUIV S (CCS_SUBST (fromList Xs Qs) C)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.EXISTS_TAC `EL n Es` \\
     CONJ_TAC (* context Xs (EL n Es) *)
     >- (MATCH_MP_TAC weakly_guarded_imp_context \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         REWRITE_TAC [MEM_EL] \\
         Q.EXISTS_TAC `n` >> art []) \\
     CONJ_TAC \\ (* 2 subgoals, same initial tactic *)
     MATCH_MP_TAC OBS_contracts_IMP_WEAK_EQUIV >|
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `!n. n < LENGTH Ps ==> X` (MP_TAC o (Q.SPEC `n`)) \\
       RW_TAC std_ss [] >> POP_ASSUM MP_TAC \\
       Know `EL n (MAP (CCS_SUBST (fromList Xs Ps)) Es) =
             CCS_SUBST (fromList Xs Ps) (EL n Es)`
       >- (MATCH_MP_TAC EL_MAP >> fs []) >> Rewr,
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `!n. n < LENGTH Qs ==> X` (MP_TAC o (Q.SPEC `n`)) \\
       RW_TAC std_ss [] >> POP_ASSUM MP_TAC \\
       Know `EL n (MAP (CCS_SUBST (fromList Xs Qs)) Es) =
             CCS_SUBST (fromList Xs Qs) (EL n Es)`
       >- (MATCH_MP_TAC EL_MAP >> fs []) >> Rewr ])
 >> POP_ASSUM K_TAC (* `n` is useless *)
 >> MATCH_MP_TAC shared_lemma
 >> fs [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
QED

(* THE FINAL THEOREM (Theorem 3.13 of [3], full version) *)
Theorem unique_solution_of_rooted_contractions :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es OBS_contracts) /\
                Qs IN (CCS_solution Xs Es OBS_contracts) ==> OBS_CONGR Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss (* `std_ss` is not enough here *)
           [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
 (* here is the difference from unique_solution_of_obs_contractions *)
 >> irule OBS_CONGR_BY_WEAK_BISIM
 >> Q.EXISTS_TAC `\R S. ?C. context Xs C /\
                            WEAK_EQUIV R (CCS_SUBST (fromList Xs Ps) C) /\
                            WEAK_EQUIV S (CCS_SUBST (fromList Xs Qs) C)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.ABBREV_TAC `P = EL n Ps` \\
     Q.ABBREV_TAC `Q = EL n Qs` \\
     Q.ABBREV_TAC `E = EL n Es` \\
     Know `weakly_guarded Xs E`
     >- (Q.UNABBREV_TAC `E` >> FIRST_X_ASSUM MATCH_MP_TAC \\
         REWRITE_TAC [MEM_EL] >> Q.EXISTS_TAC `n` >> art []) \\
     rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `OBS_contracts P (CCS_SUBST (fromList Xs Ps) E)` by METIS_TAC [EL_MAP] \\
       IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
       MP_TAC (Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma) \\
      `MEM E Es` by PROVE_TAC [MEM_EL] \\
      `FV E SUBSET (set Xs)` by PROVE_TAC [] \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E2`])) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) >> RW_TAC std_ss [] \\
      `OBS_contracts Q (CCS_SUBST (fromList Xs Qs) E)` by METIS_TAC [EL_MAP] \\
       Q.PAT_X_ASSUM `OBS_contracts P (CCS_SUBST (fromList Xs Ps) E)` K_TAC \\
       IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
       Q.EXISTS_TAC `E1'` >> art [] \\
       Q.EXISTS_TAC `E'` >> art [] \\
       MATCH_MP_TAC contracts_IMP_WEAK_EQUIV >> art [],
       (* goal 2 (of 2) *)
      `OBS_contracts Q (CCS_SUBST (fromList Xs Qs) E)` by METIS_TAC [EL_MAP] \\
       IMP_RES_TAC OBS_contracts_TRANS_LEFT \\

       MP_TAC (Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma) \\
      `MEM E Es` by PROVE_TAC [MEM_EL] \\
      `FV E SUBSET (set Xs)` by PROVE_TAC [] \\
       RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPECL [`u`, `E2'`])) >> RW_TAC std_ss [] \\
       POP_ASSUM (MP_TAC o (Q.SPEC `Ps`)) >> RW_TAC std_ss [] \\
      `OBS_contracts P (CCS_SUBST (fromList Xs Ps) E)` by METIS_TAC [EL_MAP] \\
       Q.PAT_X_ASSUM `OBS_contracts Q (CCS_SUBST (fromList Xs Qs) E)` K_TAC \\
       IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
       rename1 `WEAK_TRANS P u E1'` \\
       Q.EXISTS_TAC `E1'` >> art [] \\
       Q.EXISTS_TAC `E'` >> art [] \\
       MATCH_MP_TAC contracts_IMP_WEAK_EQUIV >> art [] ])
 >> POP_ASSUM K_TAC (* `n` is useless *)
 >> MATCH_MP_TAC shared_lemma
 >> fs [CCS_equation_def, CCS_solution_def, EVERY_MEM, LIST_REL_EL_EQN]
QED

(*   Bibliography:

 [1] Milner, R.: Communication and Concurrency. Prentice Hall International
     Series in Computer Science (1989).

 [2] Sangiorgi, D.: Equations, Contractions, and Unique Solutions.
     ACM Transactions on Computational Logic (TOCL). 18, 4:1–30 (2017).
     DOI: 10.1145/2971339

 [3] Tian, C., Sangiorgi, D.: Unique Solutions of Contractions, CCS, and
     their HOL Formalisation. Presented at the EXPRESS/SOS, August 24 (2018).
     DOI: 10.4204/EPTCS.276.10
 *)

(* for development purposes only:
 clear_overloads_on ("fromList");
 *)

val _ = export_theory ();
val _ = html_theory "Multivariate";
val _ = print_theory_to_file "-" "MultivariateTheory.lst";
