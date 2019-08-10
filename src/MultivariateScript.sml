(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Multivariate CCS Theory and Unique Solution of Equations   *)
(*                                                                            *)
(* AUTHOR        : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open listTheory alistTheory;

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

(* The use of finite_mapTheory (or alistTheory) to get rid of substitution
   orders was suggested by Konrad Slind.
 *)
val CCS_SUBST_def = Define `
   (CCS_SUBST (map :('a # ('a, 'b) CCS) list) nil = nil) /\
   (CCS_SUBST map (prefix u E) = prefix u (CCS_SUBST map E)) /\
   (CCS_SUBST map (sum E1 E2)  = sum (CCS_SUBST map E1)
                                     (CCS_SUBST map E2)) /\
   (CCS_SUBST map (par E1 E2)  = par (CCS_SUBST map E1)
                                     (CCS_SUBST map E2)) /\
   (CCS_SUBST map (restr L E)  = restr L (CCS_SUBST map E)) /\
   (CCS_SUBST map (relab E rf) = relab (CCS_SUBST map E) rf) /\
   (CCS_SUBST map (var Y)      = if (MEM Y (MAP FST map)) then THE (ALOOKUP map Y)
                                 else (var Y)) /\
   (CCS_SUBST map (rec Y E)    = if (MEM Y (MAP FST map)) then (rec Y E)
                                 else (rec Y (CCS_SUBST map E)))`;

val CCS_equation_def = Define
   `CCS_equation (Es :('a, 'b) CCS list) (Xs :'a list) <=>
      ALL_DISTINCT Xs /\ (LENGTH Es = LENGTH Xs)`;

(* solution of a CCS equation (group) up to R *)
val CCS_solution_def = Define
   `CCS_solution (R :('a, 'b) simulation) (Es :('a, 'b) CCS list) (Xs :'a list)
                 (Ps :('a, 'b) CCS list) <=>
      (LIST_REL R) Ps (MAP (CCS_SUBST (ZIP (Xs,Ps))) Es)`;

val weakly_guarded_def = Define
   `weakly_guarded Es Xs <=>
      !E X. MEM E Es /\ MEM X Xs ==> !e. CONTEXT e /\ (e (var X) = E) ==> WG e`;

(*
val STRONG_UNIQUE_SOLUTION = store_thm (
   "STRONG_UNIQUE_SOLUTION",
  ``!Es Xs. CCS_equation Es Xs /\ weakly_guarded Es Xs ==>
           !Ps Qs. Ps IN (CCS_solution STRONG_EQUIV Es Xs) /\
                   Qs IN (CCS_solution STRONG_EQUIV Es Xs) ==>
                  (LIST_REL STRONG_EQUIV) Ps Qs``,
    ...);

val UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS = store_thm (
   "UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS",
  ``!Es Xs. CCS_equation Es Xs /\ weakly_guarded Es Xs ==>
           !Ps Qs. Ps IN (CCS_solution OBS_contracts Es Xs) /\
                   Qs IN (CCS_solution OBS_contracts Es Xs) ==>
                  (LIST_REL OBS_CONGR) Ps Qs``,
    ...);
 *)

val _ = export_theory ();
val _ = html_theory "Multivariate";
