open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory combinTheory;
open stringTheory string_numTheory;
open ottTheory compTheory;

val _ = new_theory "compMeta";

Definition c_sem:
 (c_sem comp Mc (c_const cn) = Mc cn)
 /\
 (c_sem comp Mc (c_comp c1 c2) = comp (c_sem comp Mc c1) (c_sem comp Mc c2))
End

Definition S_sem:
 (S_sem comp omega MS (S_const sn) = MS sn)
 /\
 (S_sem comp omega MS (S_conj S1 S2) = S_sem comp omega MS S1 INTER S_sem comp omega MS S2)
 /\
 (S_sem comp omega MS (S_assume S1 S2) =
  { B | B IN omega /\
    !B'. B' IN S_sem comp omega MS S1 ==> comp B B' IN S_sem comp omega MS S2 })
 /\
 (S_sem comp omega MS (S_par S1 S2) = 
  { B | B IN omega /\ ?B1. ?B2. B = comp B1 B2 /\ B1 IN S_sem comp omega MS S1 /\ B2 IN S_sem comp omega MS S2 })
End

Definition P_sem:
 (P_sem comp omega Mc MS (P_implements c S) =
  (c_sem comp Mc c IN S_sem comp omega MS S))
 /\
 (P_sem comp omega Mc MS (P_refines S1 S2) =
  (S_sem comp omega MS S1 SUBSET S_sem comp omega MS S2))
 /\
 (P_sem comp omega Mc MS (P_implies P1 P2) =
  (P_sem comp omega Mc MS P1 ==> P_sem comp omega Mc MS P2))
 /\
 (P_sem comp omega Mc MS (P_and P1 P2) =
  (P_sem comp omega Mc MS P1 /\ P_sem comp omega Mc MS P2))
 /\
 (P_sem comp omega Mc MS (P_or P1 P2) =
  (P_sem comp omega Mc MS P1 \/ P_sem comp omega Mc MS P2))
 /\
 (P_sem comp omega Mc MS (P_not P) =
  ~(P_sem comp omega Mc MS P))
End

Definition spec_system_sound:
  spec_system_sound comp R omega =
  (!Mc MS G P.
    (!s. Mc s IN omega) /\
    (!s. MS s SUBSET omega) /\
    (!P0. P0 IN G ==> P_sem comp omega Mc MS P0) /\
    R G P ==>
    P_sem comp omega Mc MS P)
End

Theorem spec_holds_sound:
 !comp omega. spec_system_sound comp spec_holds omega
Proof
 failwith "FIXME"
QED

val _ = export_theory ();
