(* ========================================================================== *)
(* FILE          : MultivariateScript.sml                                     *)
(* DESCRIPTION   : Multivariate CCS Theory and Unique Solution of Equations   *)
(*                                                                            *)
(* AUTHOR        : (c) 2019 Chun Tian, Fondazione Bruno Kessler (FBK)         *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory combinTheory;

open CCSLib CCSTheory;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open BisimulationUptoTheory CongruenceTheory;
open TraceTheory ExpansionTheory ContractionTheory;

val _ = new_theory "Multivariate";
val _ = temp_loose_equality ();

(* New equivalences based on listTheory.LIST_REL *)
val _ = overload_on ("STRONG_EQL", ``LIST_REL STRONG_EQUIV``);
val _ = overload_on (  "WEAK_EQL", ``LIST_REL STRONG_EQUIV``);
val _ = overload_on (   "OBS_EQL", ``LIST_REL    OBS_CONGR``);

(* Type of all new equivalencess *)
val _ = type_abbrev_pp ("list_simulation",
      ``:('a, 'b) CCS list -> ('a, 'b) CCS list -> bool``);



val _ = export_theory ();
val _ = print_theory_to_file "-" "MultivariateTheory.lst";
val _ = html_theory "Multivariate";
