(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Multivariate CCS Theory and Unique Solution of Equations   *)
(*                                                                            *)
(* AUTHOR        : (c) 2019 Chun Tian, Fondazione Bruno Kessler (FBK)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open bisimulationTheory listTheory finite_mapTheory;

(* unused for now:
 pred_setTheory pairTheory sumTheory prim_recTheory arithmeticTheory combinTheory;
 *)

open CCSLib CCSTheory StrongEQTheory WeakEQTheory ObsCongrTheory;

(* unused for now:
open StrongEQLib StrongLawsTheory;
open WeakEQLib WeakLawsTheory;
open ObsCongrLib ObsCongrLawsTheory;
open BisimulationUptoTheory CongruenceTheory;
open TraceTheory ExpansionTheory ContractionTheory;
 *)

val _ = new_theory "Multivariate";
val _ = temp_loose_equality ();

(* New equivalences based on listTheory.LIST_REL *)
val _ = overload_on ("STRONG_EQL", ``LIST_REL STRONG_EQUIV``);
val _ = overload_on (  "WEAK_EQL", ``LIST_REL   WEAK_EQUIV``);
val _ = overload_on (   "OBS_EQL", ``LIST_REL    OBS_CONGR``);

(* Type of all new equivalencess *)
val _ = type_abbrev_pp ("list_simulation",
      ``:('a, 'b) CCS list -> ('a, 'b) CCS list -> bool``);

(* The use of finite_mapTheory to get rid of substitution orders was
   suggested by Konrad Slind. Easier than another Relabeling type.
 *)
val CCS_Subst1_def = Define `
   (CCS_Subst1 nil         (fm :'a |-> ('a, 'b) CCS) = nil) /\
   (CCS_Subst1 (prefix u E) fm = prefix u (CCS_Subst1 E fm)) /\
   (CCS_Subst1 (sum E1 E2)  fm = sum (CCS_Subst1 E1 fm)
                                     (CCS_Subst1 E2 fm)) /\
   (CCS_Subst1 (par E1 E2)  fm = par (CCS_Subst1 E1 fm)
                                     (CCS_Subst1 E2 fm)) /\
   (CCS_Subst1 (restr L E)  fm = restr L (CCS_Subst1 E fm)) /\
   (CCS_Subst1 (relab E rf) fm = relab   (CCS_Subst1 E fm) rf) /\
   (CCS_Subst1 (var Y)      fm = if (Y IN FDOM fm) then (FAPPLY fm Y)
                                 else (var Y)) /\
   (CCS_Subst1 (rec Y E)    fm = if (Y IN FDOM fm) then (rec Y E)
                                 else (rec Y (CCS_Subst1 E fm)))`;

(* :('a, 'b) CCS list -> ('a |-> ('a, 'b) CCS) -> ('a, 'b) CCS list *)
val CCS_Subst2_def = Define `
    CCS_Subst2 ES fm = MAP (\e. CCS_Subst1 e fm) ES`;

(*
val UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS = store_thm (
   "UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS",
  ``!E. WG E ==> !P Q. OBS_contracts P (E P) /\ OBS_contracts Q (E Q) ==> OBS_CONGR P Q``,
    ...);
 *)

val _ = export_theory ();
val _ = html_theory "Multivariate";
