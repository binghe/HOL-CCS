open HolKernel Parse boolLib bossLib;

open relationTheory pred_setTheory pred_setLib listTheory finite_mapTheory;

open combinTheory arithmeticTheory; (* for o_DEF and FUNPOW *)

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory WeakEQTheory TraceTheory
     ObsCongrTheory ContractionTheory CongruenceTheory BisimulationUptoTheory
     UniqueSolutionsTheory MultivariateTheory;

val _ = new_theory "leftover";


(* Some unfinished work: *)

(* Proposition 4.12 of [1], c.f. StrongLawsTheory.STRONG_UNFOLDING

   Let Es and Fs contain (free, equation) variable Es at most. Let
   As = Es{As/Xs}, Bs = Es{Bs/Xs} and Es ~ Fs. Then As ~ Bs.

Theorem strong_equiv_presd_by_rec :
    !Xs Es Fs As Bs.
        CCS_equation Xs Es /\ CCS_equation Xs Fs /\
        CCS_solution Xs Es (=) As /\
        CCS_solution Xs Fs (=) Bs /\ STRONG_EQUIV Es Fs ==> STRONG_EQUIV As Bs
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

val _ = export_theory ();
