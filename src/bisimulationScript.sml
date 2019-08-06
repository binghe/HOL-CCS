open HolKernel Parse boolLib bossLib;

open relationTheory;

val _ = new_theory "bisimulation";

(* ------------------------------------------------------------------------ *)
(*  Weak Bisimulation defind on general labelled transition relations       *)
(* ------------------------------------------------------------------------ *)

(* The "epsilon" transition: zero or more invisible actions *)
val ETS_def = Define (* was: EPS *)
   `ETS ts tau = RTC (\x y. ts x tau y)`;

(* The "weak" transition: a transition  *)
val WTS_def = Define (* was: WEAK_TRANS *)
   `WTS ts tau =
     \p l q. ?p' q'. (ETS ts tau) p p' /\ ts p' l q' /\ (ETS ts tau) q' q`;

val WBISIM_def = Define
   `WBISIM ts tau R =
     !p q. R p q ==>
          (!l. l <> tau ==>
            (!p'. ts p l p' ==> ?q'. (WTS ts tau) q l q' /\ R p' q') /\
            (!q'. ts q l q' ==> ?p'. (WTS ts tau) p l p' /\ R p' q')) /\
          (!p'. ts p tau p' ==> ?q'. (ETS ts tau) q   q' /\ R p' q') /\
          (!q'. ts q tau q' ==> ?p'. (ETS ts tau) p   p' /\ R p' q')`;

val WBISIM_REL_def = Define
   `WBISIM_REL ts tau = \p q. ?R. WBISIM ts tau R /\ R p q`;

Theorem WBISIM_INV :
    !ts tau R. WBISIM ts tau R ==> WBISIM ts tau (inv R)
Proof
    RW_TAC std_ss [WBISIM_def, inv_DEF] >> METIS_TAC []
QED

val lemma1 = prove ((* was: EPS_INDUCT *)
  ``!R. (!p q.   ts p tau q ==> R p q) /\
        (!p.     R p p) /\
        (!p q r. R p q /\ R q r ==> R p r)
    ==> !p q. (ETS ts tau) p q ==> R p q``,
    GEN_TAC >> STRIP_TAC
 >> REWRITE_TAC [ETS_def]
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> METIS_TAC []);

val lemma2 = prove ((* was: EPS_TRANS_AUX *)
  ``!p p'. (ETS ts tau) p p' ==>
           !R q. WBISIM ts tau R /\ R p q ==> ?q'. (ETS ts tau) q q' /\ R p' q'``,
    HO_MATCH_MP_TAC lemma1
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      FULL_SIMP_TAC std_ss [WBISIM_def] \\
      RES_TAC >> Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 3) *)
      FULL_SIMP_TAC std_ss [WBISIM_def] \\
      RES_TAC >> Q.EXISTS_TAC `q` \\
      ASM_REWRITE_TAC [ETS_def, RTC_REFL],
      (* goal 3 (of 3) *)
     `?q'. ETS ts tau q q' /\ R p' q'` by PROVE_TAC [] \\
     `?q''. ETS ts tau q' q'' ∧ R p'' q''` by PROVE_TAC [] \\
      Q.EXISTS_TAC `q''` >> ASM_REWRITE_TAC [] \\
      FULL_SIMP_TAC std_ss [ETS_def] \\
      MATCH_MP_TAC (REWRITE_RULE [transitive_def] RTC_TRANSITIVE) \\
      Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [] ]);

val lemma2' = prove ((* was: EPS_TRANS_AUX_SYM *)
  ``!q q'. (ETS ts tau) q q' ==>
           !R p. WBISIM ts tau R /\ R p q ==>
                 ?p'. (ETS ts tau) p p' /\ R p' q'``,
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`q`, `q'`] lemma2) >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [inv_DEF]) o (Q.SPECL [`inv R`, `p`]))
 >> IMP_RES_TAC WBISIM_INV
 >> RW_TAC std_ss []);

(*
Theorem WBISIM_O :
    !ts tau R R'. WBISIM ts tau R /\ WBISIM ts tau R' ==> WBISIM ts tau (R' O R)
Proof
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [WBISIM_def]
 >> RW_TAC std_ss [O_DEF]
 >| [ METIS_TAC [WBISIM_def],
      METIS_TAC [WBISIM_def],
      METIS_TAC [WBISIM_def, lemma2],
      METIS_TAC [WBISIM_def, lemma2'] ]
QED

Theorem WBISIM_REL_IS_EQUIV_REL :
    !ts tau. equivalence (WBISIM_REL ts tau)
Proof
  SRW_TAC[][equivalence_def]
  >- (SRW_TAC[][reflexive_def, WBISIM_REL_def] >>
      Q.EXISTS_TAC `$=` >>
      SRW_TAC[][WBISIM_def])
  >- (SRW_TAC[][symmetric_def, WBISIM_REL_def] \\
      SRW_TAC[][EQ_IMP_THM] \\
      Q.EXISTS_TAC `SC R` \\
      FULL_SIMP_TAC (srw_ss ()) [WBISIM_def, SC_DEF] \\
      METIS_TAC [])
  >- (SRW_TAC[][transitive_def, WBISIM_REL_def] >>
      Q.EXISTS_TAC `R' O R` \\
      METIS_TAC [WBISIM_O, O_DEF])
QED
*)

val _ = export_theory ();
