val (WEAK_EQUIV_rules, WEAK_EQUIV_coind, WEAK_EQUIV_cases)
  = Hol_coreln `
  !E E'.
   (!l.
     (!E1. TRANS E  (label l) E1 ==>
	   ?E2. WEAK_TRANS E' (label l) E2 /\ WEAK_EQUIV E1 E2) /\
     (!E2. TRANS E' (label l) E2 ==>
	   ?E1. WEAK_TRANS E  (label l) E1 /\ WEAK_EQUIV E1 E2)) /\
   (!E1. TRANS E  tau E1 ==> ?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2) /\
   (!E2. TRANS E' tau E2 ==> ?E1. EPS E  E1 /\ WEAK_EQUIV E1 E2)
   ==> WEAK_EQUIV E E' `;
