(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Unique Solution of Equations (Multivariate version)        *)
(*                                                                            *)
(* COPYRIGHT     : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory pred_setTheory pred_setLib listTheory finite_mapTheory;
open arithmeticTheory; (* for FUNPOW *)

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory TraceTheory
     ObsCongrTheory ContractionTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory;

val _ = new_theory "Multivariate";

val set_ss = list_ss ++ PRED_SET_ss;

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

Theorem CCS_SUBST_EMPTY :
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
 >> REWRITE_TAC [CCS_SUBST_EMPTY]
QED

(* from a key list and a value list (of same length) to an alist *)
Definition fromList_def :
    fromList (Xs :'a list) (Ps :('a, 'b) CCS list) = FEMPTY |++ ZIP (Xs,Ps)
End

val _ = overload_on ("|->", ``fromList``);
val _ = set_fixity "|->" (Infix(NONASSOC, 100));

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
Theorem CCS_SUBST_ELIM :
    !Xs E. DISJOINT (FV E) (set Xs) /\ DISJOINT (BV E) (set Xs) ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==> (CCS_SUBST (fromList Xs Ps) E = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [Once CCS_SUBST_def, BV_def, FV_def, FDOM_fromList, MAP_ZIP]
 >> `DISJOINT (FV E) (set Xs)` by ASM_SET_TAC []
 >> METIS_TAC []
QED

(* more general then CCS_SUBST_ELIM *)
Theorem CCS_SUBST_ELIM' :
    !fm E. DISJOINT (FV E) (FDOM fm) /\ DISJOINT (BV E) (FDOM fm) ==>
          (CCS_SUBST fm E = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC set_ss [Once CCS_SUBST_def, BV_def, FV_def]
 >> `DISJOINT (FV E) (FDOM fm)` by ASM_SET_TAC []
 >> METIS_TAC []
QED

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

(* CCS_SUBST_REDUCE leads to CCS_SUBST_FOLDR *)
Theorem CCS_SUBST_REDUCE :
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
 >> MATCH_MP_TAC (EQ_IMP_LR CCS_Subst_ELIM)
 >> `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL]
 >> METIS_TAC []
QED

(* CCS_SUBST_REDUCE in another form *)
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
 >> MP_TAC (REWRITE_RULE [fromList_def] (Q.SPECL [`X`,`Xs`,`r`,`Ps`] CCS_SUBST_REDUCE))
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
 >- SRW_TAC [] [FUPDATE_LIST_THM, CCS_SUBST_EMPTY]
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

(* lemma2 in another form *)
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

(* A FOLDL-like version of CCS_SUBST_REDUCE
Theorem CCS_SUBST_REDUCE' :
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
 >> SRW_TAC [] [CCS_SUBST_EMPTY, fromList_EMPTY]
 >> Q.PAT_X_ASSUM `ALL_DISTINCT Xs /\ DISJOINT (BV E) (set Xs) ==> _` MP_TAC
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`h`, `Xs`, `var h`, `MAP var Xs`] CCS_SUBST_REDUCE)
 >> `LENGTH (MAP var Xs) = LENGTH Xs` by PROVE_TAC [LENGTH_MAP]
 >> Suff `EVERY (\e. h NOTIN FV e) (MAP var Xs)` >- fs []
 >> RW_TAC std_ss [EVERY_MEM, MEM_MAP]
 >> ASM_SET_TAC [FV_def]
QED

(* ================================================================= *)
(*   Multivariate CCS contexts                                       *)
(* ================================================================= *)

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

local
  val t1 =
     (MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 + E2)`, `set Xs`] >> art [BV_SUBSETS, SUBSET_REFL]);
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

local
  val t1 =
     (MATCH_MP_TAC SUBSET_DISJOINT \\
      take [`BV (E1 || E2)`, `set Xs`] >> art [BV_SUBSETS, SUBSET_REFL]);
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

Theorem context_var :
    !Xs Y. context Xs (var Y)
Proof
    RW_TAC set_ss [context_def, EVERY_MEM, BV_def, CCS_Subst_def]
 >> Cases_on `Y = X`
 >> fs [CONTEXT_rules]
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
  ("context_rules", LIST_CONJ [context_nil,
                               context_var,
                               context_prefix_rule,
                               context_sum_rule,
                               context_par_rule,
                               context_restr_rule,
                               context_relab_rule]);

(* a collection of all backward rules of `context` *)
val context_backward_rules = save_thm
  ("context_backward_rules", LIST_CONJ [context_prefix_rule,
                                        context_sum,
                                        context_par,
                                        context_restr,
                                        context_relab,
                                        context_rec]);

(* KEY result: multivariate version of CongruenceTheory.CONTEXT_combin *)
Theorem context_combin :
    !Xs Es C. ALL_DISTINCT Xs /\ context Xs C /\
              EVERY (context Xs) Es /\ (LENGTH Xs = LENGTH Es) ==>
              context Xs (CCS_SUBST (fromList Xs Es) C)
Proof
    Suff `!Xs. ALL_DISTINCT Xs ==>
               !Es C. context Xs C ==>
                      EVERY (context Xs) Es /\ (LENGTH Xs = LENGTH Es) ==>
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
     MATCH_MP_TAC CCS_SUBST_ELIM' \\
     ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_fromList] \\
     ASM_SET_TAC [context_def])
 (* goal 8 (of 8): not hard *)
 >> Know `FDOM (fromList Xs Es) = set Xs`
 >- (MATCH_MP_TAC FDOM_fromList >> art []) >> DISCH_THEN (fs o wrap)
 >> IMP_RES_TAC context_rec
 >> Q.PAT_X_ASSUM `context Xs C' ==> _` MP_TAC >> RW_TAC std_ss []
 >> Know `CCS_SUBST (fromList Xs Es) C' = C'`
 >- (irule CCS_SUBST_ELIM >> fs [context_def])
 >> DISCH_THEN (fs o wrap)
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
         take [`BV (rec Y E)`, `set Xs`] >> art [BV_SUBSETS, SUBSET_REFL]) \\
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

(* ================================================================= *)
(*   Unique Solution of Equations                                    *)
(* ================================================================= *)

(* Lemma 4.13 in Milner's book [1] (the full version):

   If the variable X is weakly guarded in E, and E{Ps/Xs} --u-> P',
   then P' takes the form E'{Ps/Xs} (for some context E'), and
   moreover, for any Qs, E{Qs/Xs} --u-> E'{Qs/Xs}.
 *)
Theorem strong_unique_solution_lemma : (* full version *)
    !Xs E. weakly_guarded Xs E ==>
           !Ps. (LENGTH Ps = LENGTH Xs) ==>
                !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==>
                       ?E'. context Xs E' /\
                            (P' = CCS_SUBST (fromList Xs Ps) E') /\
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
    `Y NOTIN (FDOM (fromList Xs Ps))` by METIS_TAC [FDOM_fromList] \\
     fs [CCS_SUBST_def, VAR_NO_TRANS])
 (* Case 2: E = b.E' *)
 >- (rename1 `weakly_guarded Xs (prefix b E)` \\
     fs [CCS_SUBST_def, TRANS_PREFIX_EQ] \\
     Q.EXISTS_TAC `E` >> REWRITE_TAC [] \\
     IMP_RES_TAC weakly_guarded_prefix) (* for `context Xs E` *)
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
       CONJ_TAC (* context Xs (E' || E2) *)
       >- (MATCH_MP_TAC context_par_rule >> art [] \\
           MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
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
       RES_TAC >> Q.EXISTS_TAC `E1 || E''` \\
       CONJ_TAC (* context Xs (E1 || E'') *)
       >- (MATCH_MP_TAC context_par_rule >> art [] \\
           MATCH_MP_TAC weakly_guarded_imp_context >> art []) \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
       GEN_TAC >> DISCH_TAC >> DISJ2_TAC >> DISJ1_TAC \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Qs) E''` >> REWRITE_TAC [] \\
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
       CONJ_TAC (* context Xs (E' || E'') *)
       >- (MATCH_MP_TAC context_par_rule >> art []) \\
       ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
       GEN_TAC >> DISCH_TAC >> NTAC 2 DISJ2_TAC \\
       take [`CCS_SUBST (fromList Xs Qs) E'`,
             `CCS_SUBST (fromList Xs Qs) E''`, `l`] >> fs [] ])
 (* Case 5: E = restr f E' *)
 >- (IMP_RES_TAC weakly_guarded_restr \\
     fs [CCS_SUBST_def, TRANS_RESTR_EQ, FV_def] \\ (* 2 subgoals, same tactics *)
     RES_TAC >> Q.EXISTS_TAC `restr f E'` \\
     rfs [CCS_SUBST_def] \\
     MATCH_MP_TAC context_restr_rule >> art [])
 (* Case 6: E = relab E' R *)
 >- (IMP_RES_TAC weakly_guarded_relab \\
     fs [CCS_SUBST_def, TRANS_RELAB_EQ, FV_def] \\
     Q.PAT_X_ASSUM
       `!Ps. _ ==> !u P'. TRANS (CCS_SUBST (fromList Xs Ps) E) u P' ==> _`
       (MP_TAC o (Q.SPEC `Ps`)) \\
     RW_TAC std_ss [] \\
     RES_TAC >> Q.EXISTS_TAC `relab E' R` \\
     CONJ_TAC (* `context Xs (relab E' R)` *)
     >- (MATCH_MP_TAC context_relab_rule >> art []) \\
     ASM_SIMP_TAC std_ss [CCS_SUBST_def] \\
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
 >- (irule CCS_SUBST_ELIM >> art [])
 >> DISCH_THEN (fs o wrap)
 (* KEY step: let E' = P' *)
 >> Q.EXISTS_TAC `P'`
 >> Know `DISJOINT (FV P') (set Xs)`
 >- (MATCH_MP_TAC SUBSET_DISJOINT \\
     take [`FV (rec Y E) UNION BV (rec Y E)`, `set Xs`] >> art [SUBSET_REFL] \\
     CONJ_TAC >- ASM_SET_TAC [] \\
     MATCH_MP_TAC TRANS_FV \\
     Q.EXISTS_TAC `u` >> art []) >> DISCH_TAC
 >> Know `DISJOINT (BV P') (set Xs)`
 >- (MATCH_MP_TAC SUBSET_DISJOINT \\
     take [`BV (rec Y E)`, `set Xs`] >> art [SUBSET_REFL] \\
     MATCH_MP_TAC TRANS_BV \\
     Q.EXISTS_TAC `u` >> art []) >> DISCH_TAC
 >> Reverse CONJ_TAC
 >- (CONJ_TAC
     >- (MATCH_MP_TAC EQ_SYM >> irule CCS_SUBST_ELIM >> art []) \\
     rpt STRIP_TAC \\
     Know `CCS_SUBST (fromList Xs Qs) (rec Y E) = rec Y E`
     >- (irule CCS_SUBST_ELIM >> art []) >> Rewr' \\
     Know `CCS_SUBST (fromList Xs Qs) P' = P'`
     >- (irule CCS_SUBST_ELIM >> art []) >> Rewr' >> art [])
 (* context Xs P' *)
 >> RW_TAC std_ss [context_def, EVERY_MEM]
 >> Suff `!t. CCS_Subst P' t X = P'`
 >- (Rewr' >> REWRITE_TAC [CONTEXT2])
 >> REWRITE_TAC [GSYM CCS_Subst_ELIM]
 >> ASM_SET_TAC []
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

Theorem CCS_solution_LENGTH :
    !Xs Es R Ps. CCS_equation Xs Es /\ CCS_solution Xs Es R Ps ==>
                (LENGTH Ps = LENGTH Xs)
Proof
    RW_TAC list_ss [CCS_equation_def, CCS_solution_def]
 >> IMP_RES_TAC LIST_REL_LENGTH
 >> fs [LENGTH_MAP]
QED

val _ = overload_on ( "STRONG_EQUIV", ``LIST_REL  STRONG_EQUIV``);
val _ = overload_on (   "WEAK_EQUIV", ``LIST_REL    WEAK_EQUIV``);
val _ = overload_on (    "OBS_CONGR", ``LIST_REL     OBS_CONGR``);
val _ = overload_on ("OBS_contracts", ``LIST_REL OBS_contracts``);

(* Proposition 4.12 of [1], c.f. StrongLawsTheory.STRONG_UNFOLDING

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

(* Proposition 4.12 of [1], the univariate version (unconfirmed):

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

   strong_unique_solution_lemma is repeatedly used in each subgoal.

Theorem strong_unique_solution :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es STRONG_EQUIV) /\
                Qs IN (CCS_solution Xs Es STRONG_EQUIV)
            ==> LIST_REL STRONG_EQUIV Ps Qs
Proof
    rpt GEN_TAC >> REWRITE_TAC [IN_APP]
 >> RW_TAC list_ss [CCS_equation_def, CCS_solution_def, EVERY_MEM,
                    LIST_REL_EL_EQN]
 >> Q.ABBREV_TAC `P = EL n Ps`
 >> Q.ABBREV_TAC `Q = EL n Qs`
 >> irule (REWRITE_RULE [RSUBSET] STRONG_BISIM_UPTO_THM)
 >> Q.EXISTS_TAC `\x y. (x = y) \/
                        (?G. context Xs G /\
                             (x = CCS_SUBST (fromList Xs Ps) G) /\
                             (y = CCS_SUBST (fromList Xs Qs) G))`
 >> BETA_TAC >> Reverse CONJ_TAC
 >- (DISJ2_TAC >> Q.EXISTS_TAC `var (EL n Xs)` \\
     unset [`P`, `Q`] \\
     SRW_TAC [] [CCS_SUBST_def, FV_def, MEM_EL, FDOM_fromList] (* 5 subgoals *)
     >- cheat
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >- METIS_TAC []
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
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
 >> NTAC 2 POP_ORW
(* >> POP_ASSUM MP_TAC (* `FV G SUBSET set Xs` *) *)
 >> Induct_on `G` (* 8 subgoals *)
 (* Case 0: E = nil, impossible *)
 >- RW_TAC std_ss [CCS_SUBST_def, NIL_NO_TRANS]
 (* Case 1: E = var Y *)
 >- (Q.X_GEN_TAC `Y` \\
     Reverse (Cases_on `Y IN set Xs`)
     >- (`DISJOINT (FV (var Y)) (set Xs)` by ASM_SET_TAC [FV_def] \\
         `DISJOINT (BV (var Y)) (set Xs)` by ASM_SET_TAC [BV_def] \\
         `(CCS_SUBST (fromList Xs Ps) (var Y) = var Y) /\
          (CCS_SUBST (fromList Xs Qs) (var Y) = var Y)`
            by METIS_TAC [CCS_SUBST_ELIM] \\
         RW_TAC std_ss [VAR_NO_TRANS]) \\
     fs [MEM_EL] >> rename1 `i < LENGTH Xs` \\
     Know `!Zs. (LENGTH Zs = LENGTH Xs) ==>
                (CCS_SUBST (fromList Xs Zs) (var (EL i Xs)) = EL i Zs)`
     >- (RW_TAC std_ss [CCS_SUBST_def, fromList_FAPPLY_EL, FDOM_fromList] \\
         METIS_TAC [MEM_EL]) >> DISCH_TAC \\
    `(CCS_SUBST (fromList Xs Ps) (var (EL i Xs)) = EL i Ps) /\
     (CCS_SUBST (fromList Xs Qs) (var (EL i Xs)) = EL i Qs)` by PROVE_TAC [] \\
  (* applying strong_unique_solution_lemma *)
     RW_TAC std_ss [] >| (* 2 subgoals (symmetric) *)
     [ (* goal 1 (of 2) *)
      `STRONG_EQUIV (EL i Ps) (CCS_SUBST (fromList Xs Ps) (EL i Es))`
         by METIS_TAC [EL_MAP] \\
       IMP_RES_TAC PROPERTY_STAR_LEFT \\
      `weakly_guarded Xs (EL i Es)` by PROVE_TAC [] \\
       Q.ABBREV_TAC `E = EL i Es` \\
      `?E'. (E2 = CCS_SUBST (fromList Xs Ps) E') /\
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
       DISJ2_TAC >> Q.EXISTS_TAC `E'` >> REWRITE_TAC [] \\
       (* context Xs E', looks true but a proof is hard. *)
       fs [context_def, BV_def, EVERY_MEM] \\
       cheat (* weakly_guarded_def *)
       ,
       (* goal 2 (of 2) *)
      `STRONG_EQUIV (EL i Qs) (CCS_SUBST (fromList Xs Qs) (EL i Es))`
         by METIS_TAC [EL_MAP] \\
       Q.ABBREV_TAC `E = EL i Es` \\
      `?E2'. TRANS (CCS_SUBST (fromList Xs Qs) E) u E2' /\ STRONG_EQUIV E2' E2`
          by METIS_TAC [PROPERTY_STAR_LEFT, STRONG_EQUIV_SYM] \\
      `weakly_guarded Xs E` by PROVE_TAC [] \\
      `?E'. (E2' = CCS_SUBST (fromList Xs Qs) E') /\
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
       DISJ2_TAC >> Q.EXISTS_TAC `E'` >> REWRITE_TAC [] \\
       cheat (* context ... *) ])
 (* Case 2: E = prefix u G (very easy) *)
 >- cheat
 (* Case 3: E = G + G' (easy) *)
 >- cheat
 (* Case 4: E = G || G' (easy) *)
 >- cheat
 (* Case 5: E = restr f G (very easy) *)
 >- cheat
 (* Case 6: E = relab f G (very easy) *)
 >- cheat
 (* Case 7: E = rec Y G (done, `context Xs` is essential here) *)
 >> POP_ASSUM K_TAC (* IH is not used here, removed *)
 >> Q.X_GEN_TAC `Y` >> DISCH_TAC
 >> IMP_RES_TAC context_rec
 >> `DISJOINT (FV (rec Y G)) (set Xs)` by ASM_SET_TAC [FV_def]
 >> `DISJOINT (BV (rec Y G)) (set Xs)` by ASM_SET_TAC [context_def]
 >> `(CCS_SUBST (fromList Xs Ps) (rec Y G) = rec Y G) /\
     (CCS_SUBST (fromList Xs Qs) (rec Y G) = rec Y G)`
        by METIS_TAC [CCS_SUBST_ELIM] >> NTAC 2 POP_ORW
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

val CCS_unfolding_lemma1 = Q.prove (
   `!Xs Es E C C' Ps.
        CCS_equation Xs Es /\ EVERY (context Xs) Es /\
        CCS_solution Xs Es OBS_contracts Ps /\ context Xs C /\
        (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) /\
        (C' = \n. CCS_SUBST (fromList Xs (FUNPOW E n (MAP var Xs))) C)
    ==> !n. OBS_contracts (CCS_SUBST (fromList Xs Ps) C)
                          (CCS_SUBST (fromList Xs Ps) (C' n))`,
    cheat);

val CCS_unfolding_lemma4 = Q.prove (
   `!Xs Es Ps E C C' n xs P'.
        CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es /\
        CCS_solution Xs Es OBS_contracts Ps /\ context Xs C /\
        (E = \Ys. MAP (CCS_SUBST (fromList Xs Ys)) Es) /\
        (C' = \n. CCS_SUBST (fromList Xs (FUNPOW E n (MAP var Xs))) C) /\
        TRACE (CCS_SUBST (fromList Xs Ps) (C' n)) xs P' /\ (LENGTH xs <= n) ==>
        ?C''. context Xs C'' /\ (P' = CCS_SUBST (fromList Xs Ps) C'') /\
             !Qs. (LENGTH Qs = LENGTH Xs) ==>
                  TRACE (CCS_SUBST (fromList Xs Qs) (C' n)) xs
                        (CCS_SUBST (fromList Xs Qs) C'')`,
    cheat);

(* Lemma 3.9 of [2], full/multivariate version of
   UniqueSolutionsTheory.UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA *)
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
 (* useless assumptions:
 >> Know `E (MAP var Xs) = Es`
 >- (Q.UNABBREV_TAC `E` >> BETA_TAC \\
     RW_TAC list_ss [] \\
     MATCH_MP_TAC LIST_EQ >> RW_TAC list_ss [LENGTH_MAP, EL_MAP] \\
     MATCH_MP_TAC CCS_SUBST_self \\
     fs [CCS_equation_def, EVERY_MEM, weakly_guarded_def, MEM_EL] \\
     METIS_TAC []) >> DISCH_TAC
 >> Know `C' 0 = C`
 >- (Q.UNABBREV_TAC `C'` >> SIMP_TAC std_ss [FUNPOW_0] \\
     MATCH_MP_TAC CCS_SUBST_self \\
     PROVE_TAC [context_def, CCS_equation_def])
 >> DISCH_TAC
  *)
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
 >- (MATCH_MP_TAC CCS_unfolding_lemma1 \\
     take [`Es`, `E`] >> unset [`E`, `C'`] >> art [])
 >> DISCH_TAC
 >> Know `!n. OBS_contracts (CCS_SUBST (fromList Xs Qs) C)
                            (CCS_SUBST (fromList Xs Qs) (C' n))`
 >- (MATCH_MP_TAC CCS_unfolding_lemma1 \\
     take [`Es`, `E`] >> unset [`E`, `C'`] >> art [])
 >> DISCH_TAC
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
      >- (MATCH_MP_TAC CCS_unfolding_lemma4 \\
          take [`Es`, `E`, `C`] >> unset [`E`, `C'`] >> art []) \\
      STRIP_TAC >> POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) \\
     `LENGTH Qs = LENGTH Xs` by PROVE_TAC [CCS_solution_LENGTH] \\
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
      >- (MATCH_MP_TAC CCS_unfolding_lemma4 \\
          take [`Es`, `E`, `C`] >> unset [`E`, `C'`] >> art []) \\
      STRIP_TAC >> POP_ASSUM (MP_TAC o (Q.SPEC `Qs`)) \\
     `LENGTH Qs = LENGTH Xs` by PROVE_TAC [CCS_solution_LENGTH] \\
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
    rpt STRIP_TAC
 >> REWRITE_TAC [WEAK_BISIM]
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
                Qs IN (CCS_solution Xs Es OBS_contracts)
            ==> LIST_REL WEAK_EQUIV Ps Qs
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
     CONJ_TAC (* 2 subgoals, same initial tactic *) \\
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

(* THE FINAL THEOREM (it additionally uses "strong_unique_solution_lemma") *)
Theorem unique_solution_of_rooted_contractions :
    !Xs Es. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
        !Ps Qs. Ps IN (CCS_solution Xs Es OBS_contracts) /\
                Qs IN (CCS_solution Xs Es OBS_contracts)
            ==> LIST_REL OBS_CONGR Ps Qs
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
       Q.PAT_X_ASSUM `weakly_guarded Xs E`
         (MP_TAC o (Q.SPEC `Ps`) o (MATCH_MP strong_unique_solution_lemma)) \\
       RW_TAC std_ss [] >> RES_TAC \\
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
       Q.PAT_X_ASSUM `weakly_guarded Xs E`
         (MP_TAC o (Q.SPEC `Qs`) o (MATCH_MP strong_unique_solution_lemma)) \\
       RW_TAC std_ss [] >> RES_TAC \\
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

(* Bibliography:
 *
 * [1] Milner, R.: Communication and Concurrency. Prentice Hall International
 *     Series in Computer Science (1989).
 * [2] Sangiorgi, D.: Equations, Contractions, and Unique Solutions.
 *     ACM Transactions on Computational Logic (TOCL). 18, 4:1–30 (2017).
 *)

val _ = export_theory ();
val _ = html_theory "Multivariate";
