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

(*

(* THE STAGE THEOREM:
   Let the expression Es contain at most Xs, and let Xs be weakly guarded in Es,
   then:
        If Ps ~ E{Ps/Xs} and Qs ~ E{Qs/Xs} then Ps ~ Qs.
 *)
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
 (* `FV G SUBSET (set Xs)` is necessary in the case of `par`,
     also changed `x = CCS_SUBST (fromList Xs Ps) G` to
    `STRONG_EQUIV x (CCS_SUBST (fromList Xs Ps) G)` for the case of `par`.
  *)
 >> Q.EXISTS_TAC `\x y. (x = y) \/
                        (?G. context Xs G /\ (FV G) SUBSET (set Xs) /\
                             (STRONG_EQUIV x (CCS_SUBST (fromList Xs Ps) G)) /\
                             (STRONG_EQUIV y (CCS_SUBST (fromList Xs Qs) G)))`
 >> BETA_TAC >> Reverse CONJ_TAC
 >- (DISJ2_TAC >> Q.EXISTS_TAC `var (EL n Xs)` \\
     unset [`P`, `Q`] \\
     SRW_TAC [] [CCS_SUBST_def, FV_def, MEM_EL, FDOM_fromList] (* 6 subgoals *)
     >- REWRITE_TAC [context_var]
     >- (Q.EXISTS_TAC `n` >> art [])
     >- (Suff `EL n Ps = fromList Xs Ps ' (EL n Xs)` >- rw [STRONG_EQUIV_REFL] \\
         MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >- (Suff `EL n Ps = var (EL n Xs)` >- rw [STRONG_EQUIV_REFL] \\
         METIS_TAC [])
     >- (Suff `EL n Qs = fromList Xs Qs ' (EL n Xs)` >- rw [STRONG_EQUIV_REFL] \\
         MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC fromList_FAPPLY_EL >> art [])
     >> (Suff `EL n Qs = var (EL n Xs)` >- rw [STRONG_EQUIV_REFL] \\
         METIS_TAC []))
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
 >> unset [`P`, `Q`]
 >> Q.PAT_X_ASSUM `n < LENGTH Xs` K_TAC
 >> Induct_on `G` (* 8 subgoals *)
 (* Case 0: G = nil, impossible *)
 >- (RW_TAC std_ss [CCS_SUBST_def, FV_def] \\ (* 2 goals *)
     IMP_RES_TAC PROPERTY_STAR_LEFT >> fs [NIL_NO_TRANS])
 (* Case 1: G = var Y *)
 >- (Q.X_GEN_TAC `Y` >> NTAC 4 STRIP_TAC \\
     Reverse (Cases_on `Y IN set Xs`) (* impossible case *)
     >- (`DISJOINT (FV (var Y)) (set Xs)` by ASM_SET_TAC [FV_def] \\
         `DISJOINT (BV (var Y)) (set Xs)` by ASM_SET_TAC [BV_def] \\
         `(CCS_SUBST (fromList Xs Ps) (var Y) = var Y) /\
          (CCS_SUBST (fromList Xs Qs) (var Y) = var Y)`
             by METIS_TAC [CCS_SUBST_elim] >> fs [] \\
          RW_TAC std_ss [] \\
          IMP_RES_TAC PROPERTY_STAR_LEFT >> fs [VAR_NO_TRANS]) \\
     fs [MEM_EL] >> rename1 `i < LENGTH Xs` \\
     Know `!Zs. (LENGTH Zs = LENGTH Xs) ==>
                (CCS_SUBST (fromList Xs Zs) (var Y) = EL i Zs)`
     >- (RW_TAC std_ss [CCS_SUBST_def, fromList_FAPPLY_EL, FDOM_fromList] \\
         METIS_TAC [MEM_EL]) >> DISCH_TAC \\
    `(CCS_SUBST (fromList Xs Ps) (var Y) = EL i Ps) /\
     (CCS_SUBST (fromList Xs Qs) (var Y) = EL i Qs)` by PROVE_TAC [] \\
     Q.ABBREV_TAC `P = EL i Ps` \\
     Q.ABBREV_TAC `Q = EL i Qs` \\
     Q.ABBREV_TAC `E = EL i Es` \\
     fs [] >> rpt STRIP_TAC >| (* 2 subgoals (symmetric) *)
     [ (* goal 1 (of 2):
             ?E1'   ~     E'[Qs/Xs] .............
              |           |                     .
              u           u                     .
              |           |                     .
              Q'  ~ Q   ~ E[Qs/Xs]              .
                                                .
              P'  ~ P   ~ E[Ps/Xs]              .
              |     |     |                     .
              u     u     u                     .
              |     |     |                     .
              E1  ~ E2' ~ E2 = E'[Ps/Xs] ........
        *)
      `STRONG_EQUIV P (CCS_SUBST (fromList Xs Ps) E)` by METIS_TAC [EL_MAP] \\
      `?E2'. TRANS P u E2' /\ STRONG_EQUIV E1 E2'` by PROVE_TAC [PROPERTY_STAR] \\
      `?E2. TRANS (CCS_SUBST (fromList Xs Ps) E) u E2 /\ STRONG_EQUIV E2' E2`
          by PROVE_TAC [PROPERTY_STAR] \\
      `weakly_guarded Xs E /\ FV E SUBSET (set Xs)` by PROVE_TAC [] \\
      `?E'. context Xs E' /\ FV E' SUBSET (set Xs) /\
            (E2 = CCS_SUBST (fromList Xs Ps) E') /\
            !Qs. (LENGTH Qs = LENGTH Xs) ==>
                 TRANS (CCS_SUBST (fromList Xs Qs) E) u
                       (CCS_SUBST (fromList Xs Qs) E')`
          by METIS_TAC [Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma] \\
      `STRONG_EQUIV Q (CCS_SUBST (fromList Xs Qs) E)` by METIS_TAC [EL_MAP] \\
      `TRANS (CCS_SUBST (fromList Xs Qs) E) u (CCS_SUBST (fromList Xs Qs) E')`
          by PROVE_TAC [] \\
      `STRONG_EQUIV Q' (CCS_SUBST (fromList Xs Qs) E)`
          by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `?E1'. TRANS Q' u E1' /\
             STRONG_EQUIV E1' (CCS_SUBST (fromList Xs Qs) E')`
          by PROVE_TAC [PROPERTY_STAR] \\
       Q.EXISTS_TAC `E1'` >> ASM_SIMP_TAC std_ss [O_DEF] \\
       Q.EXISTS_TAC `E1'` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E1` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
       DISJ2_TAC >> Q.EXISTS_TAC `E'` >> art [] \\
       MATCH_MP_TAC STRONG_EQUIV_TRANS \\
       Q.EXISTS_TAC `E2'` >> PROVE_TAC [],
       (* goal 2 (of 2):
             ?E2'   ~     E'[Ps/Xs] .............
              |           |                     .
              u           u                     .
              |           |                     .
              P'  ~ P   ~ E[Ps/Xs]              .
                                                .
              Q'  ~ Q   ~ E[Qs/Xs]              .
              |     |     |                     .
              u     u     u                     .
              |     |     |                     .
              E2  ~ E1' ~ E1 = E'[Qs/Xs] ........
        *)
      `STRONG_EQUIV Q (CCS_SUBST (fromList Xs Qs) E)` by METIS_TAC [EL_MAP] \\
      `?E1'. TRANS Q u E1' /\ STRONG_EQUIV E2 E1'` by PROVE_TAC [PROPERTY_STAR] \\
      `?E1. TRANS (CCS_SUBST (fromList Xs Qs) E) u E1 /\ STRONG_EQUIV E1' E1`
          by PROVE_TAC [PROPERTY_STAR] \\
      `weakly_guarded Xs E /\ FV E SUBSET (set Xs)` by PROVE_TAC [] \\
      `?E'. context Xs E' /\ FV E' SUBSET (set Xs) /\
            (E1 = CCS_SUBST (fromList Xs Qs) E') /\
            !Ps. (LENGTH Ps = LENGTH Xs) ==>
                 TRANS (CCS_SUBST (fromList Xs Ps) E) u
                       (CCS_SUBST (fromList Xs Ps) E')`
         by METIS_TAC [Q.SPECL [`Xs`, `E`] strong_unique_solution_lemma] \\
      `STRONG_EQUIV P (CCS_SUBST (fromList Xs Ps) E)` by METIS_TAC [EL_MAP] \\
      `TRANS (CCS_SUBST (fromList Xs Ps) E) u (CCS_SUBST (fromList Xs Ps) E')`
         by PROVE_TAC [] \\
      `STRONG_EQUIV P' (CCS_SUBST (fromList Xs Ps) E)`
         by PROVE_TAC [STRONG_EQUIV_TRANS] \\
      `?E2'. TRANS P' u E2' /\
             STRONG_EQUIV E2' (CCS_SUBST (fromList Xs Ps) E')`
          by PROVE_TAC [PROPERTY_STAR] \\
       Q.EXISTS_TAC `E2'` >> ASM_SIMP_TAC std_ss [O_DEF] \\
       Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `CCS_SUBST (fromList Xs Ps) E'` >> art [] \\
       DISJ2_TAC >> Q.EXISTS_TAC `E'` >> art [STRONG_EQUIV_REFL] \\
       MATCH_MP_TAC STRONG_EQUIV_TRANS \\
       Q.EXISTS_TAC `E1'` >> PROVE_TAC [] ])
 (* Case 2: E = prefix u G (not easy) *)
 >- (RW_TAC std_ss [FV_def, context_prefix_rewrite, CCS_SUBST_prefix] >|
     [ (* goal 1 (of 2) *)
      `?E2. (prefix 
 cheat
     

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
         cheat (* but possible *),
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
         cheat (* but impossible unless ... *) ],
       (* goal 2 (of 6) *)
       cheat,
       (* goal 3 (of 6) *)
       cheat,
       (* goal 4 (of 6) *)
       cheat,
       (* goal 5 (of 6) *)
       cheat,
       (* goal 6 (of 6) *)
       cheat ])
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
(* for development purposes only:
 clear_overloads_on ("fromList");
 *)

val _ = export_theory ();
