open HolKernel Parse boolLib bossLib;

open relationTheory optionTheory; (* listTheory *)

val _ = new_theory "bisimulation";

(* ------------------------------------------------------------------------ *)
(*  Strong Bisimulation defind on general labelled transition relations     *)
(* ------------------------------------------------------------------------ *)

(* the start point is the following code contributed by James Shaker:

val BISIM_def = Define
   `BISIM (ts :'a->'b->'a->bool) (R :'a->'a->bool) =
    !p q l. R p q ==>
            (!p'. ts p l p' ==> (?q'. ts q l q' /\ R p' q')) /\
            (!q'. ts q l q' ==> (?p'. ts p l p' /\ R p' q'))`;

val BISIM_REL_def = Define
   `BISIM_REL ts p q = ?R. BISIM ts R /\ R p q`;
 *)

Theorem BISIM_ID :
    !ts. BISIM ts Id
Proof
    RW_TAC std_ss [BISIM_def]
QED

Theorem BISIM_INV :
    !ts R. BISIM ts R ==> BISIM ts (inv R)
Proof
    RW_TAC std_ss [BISIM_def, inv_DEF] >> METIS_TAC []
QED

Theorem BISIM_O :
    !ts R R'. BISIM ts R /\ BISIM ts R' ==> BISIM ts (R' O R)
Proof
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [BISIM_def]
 >> RW_TAC std_ss [O_DEF]
 >> METIS_TAC [BISIM_def]
QED

Theorem BISIM_RUNION :
    !ts R R'. BISIM ts R /\ BISIM ts R' ==> BISIM ts (R RUNION R')
Proof
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [BISIM_def]
 >> RW_TAC std_ss [RUNION]
 >> METIS_TAC []
QED

(*
Theorem BISIM_REL_IS_EQUIV_REL :
    !ts. equivalence (BISIM_REL ts)
Proof
    SRW_TAC[][equivalence_def]
 >- (SRW_TAC[][reflexive_def, BISIM_REL_def] \\
     Q.EXISTS_TAC `Id` \\
     REWRITE_TAC [BISIM_ID])
 >- (SRW_TAC[][symmetric_def, BISIM_REL_def] \\
     SRW_TAC[][EQ_IMP_THM] \\
     Q.EXISTS_TAC `SC R` \\
     FULL_SIMP_TAC (srw_ss ()) [BISIM_def, SC_DEF] \\
     METIS_TAC[])
 >- (SRW_TAC[][transitive_def, BISIM_REL_def] \\
     Q.EXISTS_TAC `R' O R` \\
     METIS_TAC [O_DEF, BISIM_O])
QED
*)

(* ------------------------------------------------------------------------ *)
(*  Weak Bisimulation defind on general labelled transition relations       *)
(* ------------------------------------------------------------------------ *)

(* IMPORTANT: this definition is wrong due to missing of WEAK_TRANS *)
val WBISIM_def = new_definition (
   "WBISIM_def",
  ``WBISIM (ts :'a->'b option->'a->bool) (R :'a->'a->bool) =
    !p q l. R p q ==>
      (!p'. ts p (SOME l) p' ==> (?q'. ts q (SOME l) q' /\ R p' q')) /\
      (!q'. ts q (SOME l) q' ==> (?p'. ts p (SOME l) p' /\ R p' q')) /\
      (!p'. ts p NONE p' ==> (?q'. RTC (\x y. ts x NONE y) q q' /\ R p' q')) /\
      (!q'. ts q NONE q' ==> (?p'. RTC (\x y. ts x NONE y) p p' /\ R p' q'))``);

val WBISIM_REL_def = new_definition (
   "WBISIM_REL_def",
  ``WBISIM_REL ts p q = ?R. WBISIM ts R /\ R p q``);

Theorem WBISIM_INV :
   !ts R. WBISIM ts R ==> WBISIM ts (inv R)
Proof
    RW_TAC std_ss [WBISIM_def, inv_DEF] >> METIS_TAC []
QED

val lemma1 = prove ((* was: EPS_INDUCT *)
  ``!R. (!p q.   ts p NONE q ==> R p q) /\
        (!p.     R p p) /\
        (!p q r. R p q /\ R q r ==> R p r)
    ==> !p q. (RTC (\x y. ts x NONE y)) p q ==> R p q``,
    GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC RTC_INDUCT
 >> METIS_TAC []);

val lemma2 = prove ((* was: EPS_TRANS_AUX *)
  ``!p p'. RTC (\x y. ts x NONE y) p p' ==>
           !R q. WBISIM ts R /\ R p q ==>
                 ?q'. RTC (\x y. ts x NONE y) q q' /\ R p' q'``,
    HO_MATCH_MP_TAC lemma1
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      FULL_SIMP_TAC std_ss [WBISIM_def] \\
      RES_TAC >> Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 3) *)
      FULL_SIMP_TAC std_ss [WBISIM_def] \\
      RES_TAC >> Q.EXISTS_TAC `q` >> ASM_REWRITE_TAC [RTC_REFL],
      (* goal 3 (of 3) *)
      Q.ABBREV_TAC `EPS = RTC (\x y. ts x NONE y)` \\
     `?q'. EPS q q' /\ R p' q'` by PROVE_TAC [] \\
     `?q''. EPS q' q'' ∧ R p'' q''` by PROVE_TAC [] \\
      Q.EXISTS_TAC `q''` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `EPS` \\
      MATCH_MP_TAC (REWRITE_RULE [transitive_def]
                                 RTC_TRANSITIVE) \\
      Q.EXISTS_TAC `q'` >> ASM_REWRITE_TAC [] ]);

val lemma2' = prove ((* was: EPS_TRANS_AUX_SYM *)
  ``!q q'. RTC (\x y. ts x NONE y) q q' ==>
           !R p. WBISIM ts R /\ R p q ==>
                 ?p'. RTC (\x y. ts x NONE y) p p' /\ R p' q'``,
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`q`, `q'`] lemma2) >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [inv_DEF]) o (Q.SPECL [`inv R`, `p`]))
 >> IMP_RES_TAC WBISIM_INV
 >> RW_TAC std_ss []);

Theorem WBISIM_O :
    !ts R R'. WBISIM ts R /\ WBISIM ts R' ==> WBISIM ts (R' O R)
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
    !ts. equivalence (WBISIM_REL ts)
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

val _ = export_theory ();
