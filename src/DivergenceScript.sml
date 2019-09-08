(* ========================================================================== *)
(* FILE          : DivergenceScript.sml                                       *)
(* DESCRIPTION   : Divergence and Unique Solution of Equations                *)
(*                                                                            *)
(* COPYRIGHT     : (c) 2019 Chun Tian, Fondazione Bruno Kessler, Italy        *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory pred_setTheory pred_setLib listTheory finite_mapTheory;
open combinTheory arithmeticTheory; (* for o_DEF and FUNPOW *)

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory TraceTheory
     ObsCongrTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory MultivariateTheory;

val _ = new_theory "Divergence";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.

 [2] Durier, A., Hirschkoff, D., Sangiorgi, D.: Divergence and Unique
     Solution of Equations. Log.Meth.Comput.Sci. 15, 12:1–12:34 (2019).
 *)

val _ = export_theory ();
val _ = html_theory "Divergence";
val _ = print_theory_to_file "-" "DivergenceTheory.lst";
