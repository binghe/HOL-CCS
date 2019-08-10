(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Multivariate CCS Theory and Unique Solution of Equations   *)
(*                                                                            *)
(* AUTHOR        : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open listTheory finite_mapTheory;

(* unused for now:
 pred_setTheory pairTheory sumTheory prim_recTheory arithmeticTheory combinTheory;
 *)

open CCSLib CCSTheory StrongEQTheory WeakEQTheory ObsCongrTheory
     ContractionTheory CongruenceTheory UniqueSolutionsTheory;

(* unused for now:
open StrongEQLib StrongLawsTheory;
open WeakEQLib WeakLawsTheory;
open ObsCongrLib ObsCongrLawsTheory;
open BisimulationUptoTheory;
open TraceTheory ExpansionTheory ;
 *)

val _ = new_theory "Multivariate";

(* DESIGN NOTES

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

   The `=` (at left) could be `STRONG_EQUIV`, `WEAK_EQUIV`, `OBS_CONGR` or even
   `contracts`. (In case of `contracts` it's actually an inequation group.)

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

      `Ps IN (CCS_solution Es Xs) /\ Qs IN (CCS_solution Es Xs)`, or
      `CCS_solution Es Xs Ps /\ CCS_solution Es Xs Qs`,

   then, beside ``Ps = Qs`, we may also have:

      `STRONG_EQL Ps Qs` (`LIST_REL STRONG_EQUIV Ps Qs`), or
      `WEAL_EQL Ps Qs` (`LIST_REL WEAK_EQUIV Ps Qs`), or
      `OBS_EQL Ps Qs` (`LIST_REL OBS_EQUIV Ps Qs`)   

   Ps (or Qs) is called an "unique" solution (up to the corresponding
   equivalence relation).

4. What's a "weakly guarded" multivariate CCS equation (group)?

  `weakly_guarded Es Xs` means, for each E in Es,
  `weakly_guarded1 E Xs`, which further means, for each X in Xs, if X appears
   in E (otherwise E is directly weak-guarded according to [WG2]), then
   for all CONTEXT e such that C[var X] = E, we have the "hole(s)" in C is weakly-guarded:

   weakly_guarded Es Xs =
     !E X. MEM E Es /\ MEM X Xs ==> !e. CONTEXT e /\ (e (var X) = E) ==> WG e
  
   NOTE 1: using `?e. (e (var X) = E) /\ WG e` is wrong, because `E` may
   contain multiple `var X` as free variables, thus it's possible
   that there exists two different CONTEXTs, say e1 and e2, such that

     e1 <> e2 /\ (e1 (var X) = E) /\ (e2 (var X) = E) /\ WG e1 /\ WG e2

   but none of them are really weakly guarded for all appearences of
   (var X) in E.  Thus the `forall` quantifier is a MUST.

   NOTE 2: the "weak guardedness" of Es is always connected with Xs,
   as we don't need to care about those (free) variables in Es that
   are outside of Xs. Even they're not weakly guarded, we don't care,
   as they will be never substituted as an equation variable, instead
   they just function like a nil (with no further transition).  In
   this way, we eliminated the needs of using possibly-wrong
   definition of FV (the set/list of free variables), as the same
   variable may appear both free and bounded in different sub-term of
   the same CCS term.

   Finally, there's a limitation that, the (current) definition of WG
   doesn't have any recursion operator (unless inside `p` of
   `\t. p`). This means, our equation (free) variables can never be
   wrapped by another bounded variable in the CCS equations.  Fixing
   this limitation may falsify the entire unique-solution of
   contraction theorm as I currently observed (but didn't say anywhere
   else), simply because certain proof steps cannot be fixed under
   this possibility. This is a potential TODO direction in the future.

*)

(* The use of finite_mapTheory to get rid of substitution orders was
   suggested by Konrad Slind (HOL mailing list on Oct 23, 2017):

   "There are all kinds of issues with substitutions and applying them to term-like
    structures. I would probably start by choosing finite maps (finite_mapTheory) as 
    the representation for variable substitutions since they get rid of most if not all
    the issues with ordering of replacements. The alistTheory provides a more 
    computationally friendly version, and provides a formal connection
    back to fmaps.

    Also see <holdir>/examples/unification/triangular/first-order 
    for a unification case study."
 *)
val CCS_SUBST_def = Define `
   (CCS_SUBST (fm :'a |-> ('a, 'b) CCS) nil = nil) /\
   (CCS_SUBST fm (prefix u E) = prefix u (CCS_SUBST fm E)) /\
   (CCS_SUBST fm (sum E1 E2)  = sum (CCS_SUBST fm E1)
                                    (CCS_SUBST fm E2)) /\
   (CCS_SUBST fm (par E1 E2)  = par (CCS_SUBST fm E1)
                                    (CCS_SUBST fm E2)) /\
   (CCS_SUBST fm (restr L E)  = restr L (CCS_SUBST fm E)) /\
   (CCS_SUBST fm (relab E rf) = relab (CCS_SUBST fm E) rf) /\
   (CCS_SUBST fm (var Y)      = if Y IN FDOM fm then fm ' Y else (var Y)) /\
   (CCS_SUBST fm (rec Y E)    = if Y IN FDOM fm then (rec Y E)
                                else (rec Y (CCS_SUBST fm E)))`;

val CCS_equation_def = Define
   `CCS_equation (Xs :'a list) (Es :('a, 'b) CCS list) <=>
      ALL_DISTINCT Xs /\ (LENGTH Xs = LENGTH Es)`;

(* This is again inspired from Konrad Slind (HOL mailing list on Aug 7, 2019):
   "See also examples/balanced_bst/balanced_mapTheory, which has a 'fromList' construct."
 *)
val fromList_def = Define
   `fromList Xs Ps = FEMPTY |++ (ZIP (Xs,Ps))`;

Theorem IN_fromList :
    !X Xs Ps. X IN FDOM (fromLists Xs Ps) <=> MEM X Xs
Proof
    cheat
QED

(* A solution of the CCS equation (group) Es[Xs] upto R *)
val CCS_solution_def = Define
   `CCS_solution (Ps :('a, 'b) CCS list)
                 (R  :('a, 'b) simulation)
                 (Es :('a, 'b) CCS list) (Xs :'a list) <=>
      (LIST_REL R) Ps (MAP (CCS_SUBST (fromList Xs Ps)) Es)`;

val weakly_guarded_def = Define
   `weakly_guarded Xs = \E. EVERY (\x. WG (\t. CCS_Subst E t x)) Xs`;

Theorem weakly_guarded_alt :
    !Xs Es. EVERY (weakly_guarded Xs) Es <=>
            !E X. MEM E Es /\ MEM X Xs ==> WG (\t. CCS_Subst E t X)
Proof
    cheat
QED

val _ = overload_on ("STRONG_EQUIV", ``LIST_REL STRONG_EQUIV``);
val _ = overload_on (  "WEAK_EQUIV", ``LIST_REL   WEAK_EQUIV``);
val _ = overload_on (   "OBS_CONGR", ``LIST_REL    OBS_CONGR``);

Theorem STRONG_UNIQUE_SOLUTION_MULTI :
    !Es Xs. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
            !Ps Qs. CCS_solution Ps STRONG_EQUIV Es Xs /\
                    CCS_solution Qs STRONG_EQUIV Es Xs ==>
                   (LIST_REL STRONG_EQUIV) Ps Qs
Proof
    cheat
QED

(* THE FINAL THEOREM *)
Theorem UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS_MULTI :
    !Es Xs. CCS_equation Xs Es /\ EVERY (weakly_guarded Xs) Es ==>
            !Ps Qs. CCS_solution Ps OBS_contracts Es Xs /\
                    CCS_solution Qs OBS_contracts Es Xs ==>
                   (LIST_REL OBS_CONGR) Ps Qs
Proof
    cheat
QED

val _ = export_theory ();
val _ = html_theory "Multivariate";
