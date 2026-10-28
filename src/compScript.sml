open HolKernel boolLib Parse bossLib ottLib;
infix THEN THENC |-> ## ;
local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory 
  finite_mapTheory in end;

val _ = new_theory "comp";

open string_numTheory;

Type cn = ``:string`` (* component constant name *)
Type Sn = ``:string`` (* specification constant name *)
val _ = Hol_datatype ` 
c =  (* component term *)
   c_const of cn (* constant *)
 | c_comp of c => c (* composition *)
`;
val _ = Hol_datatype ` 
S =  (* specification term *)
   S_const of Sn (* constant *)
 | S_conj of S => S (* conjunction *)
 | S_assume of S => S (* assume-guarantee *)
 | S_par of S => S (* parallel *)
`;
val _ = Hol_datatype ` 
P =  (* predicate *)
   P_implements of c => S (* implements *)
 | P_refines of S => S (* refines *)
 | P_implies of P => P (* implies *)
 | P_and of P => P (* conjunction *)
 | P_or of P => P (* disjunction *)
 | P_not of P (* negation *)
`;

Type G = ``:(P set)``
(** definitions *)

(* defns spec_proof *)
Inductive spec_proof:
(* defn spec_holds *)

[ax:] (! (G:G) (P:P) .
(clause_name "ax")
 ==> 
( ( spec_holds  ( P  INSERT  G )  P )))

[ref_el:] (! (G:G) (c:c) (S2:S) (S1:S) .
(clause_name "ref_el") /\
(( ( spec_holds G (P_implements c S1) )) /\
( ( spec_holds G (P_refines S1 S2) )))
 ==> 
( ( spec_holds G (P_implements c S2) )))

[conj_in:] (! (G:G) (c:c) (S1:S) (S2:S) .
(clause_name "conj_in") /\
(( ( spec_holds G (P_implements c S1) )) /\
( ( spec_holds G (P_implements c S2) )))
 ==> 
( ( spec_holds G (P_implements c (S_conj S1 S2)) )))

[conj_el1:] (! (G:G) (c:c) (S1:S) (S2:S) .
(clause_name "conj_el1") /\
(( ( spec_holds G (P_implements c (S_conj S1 S2)) )))
 ==> 
( ( spec_holds G (P_implements c S1) )))

[conj_el2:] (! (G:G) (c:c) (S2:S) (S1:S) .
(clause_name "conj_el2") /\
(( ( spec_holds G (P_implements c (S_conj S1 S2)) )))
 ==> 
( ( spec_holds G (P_implements c S2) )))

[par_in:] (! (G:G) (c1:c) (c2:c) (S1:S) (S2:S) .
(clause_name "par_in") /\
(( ( spec_holds G (P_implements c1 S1) )) /\
( ( spec_holds G (P_implements c2 S2) )))
 ==> 
( ( spec_holds G (P_implements (c_comp c1 c2) (S_par S1 S2)) )))

[cont_el:] (! (G:G) (c1:c) (c2:c) (S2:S) (S1:S) .
(clause_name "cont_el") /\
(( ( spec_holds G (P_implements c1 S1) )) /\
( ( spec_holds G (P_implements c2 (S_assume S1 S2)) )))
 ==> 
( ( spec_holds G (P_implements (c_comp c1 c2) S2) )))

[cre:] (! (G:G) (c:c) (S2:S) (S3:S) (S1:S) .
(clause_name "cre") /\
(( ( spec_holds G (P_implements c (S_conj S1 S2)) )) /\
( ( spec_holds G (P_refines S2 S3) )))
 ==> 
( ( spec_holds G (P_implements c (S_conj S2 S3)) )))

[cr:] (! (G:G) (c:c) (S2:S) (S3:S) (S1:S) .
(clause_name "cr") /\
(( ( spec_holds G (P_implements c (S_conj S1 S3)) )) /\
( ( spec_holds G (P_refines S1 S2) )))
 ==> 
( ( spec_holds G (P_implements c (S_conj S2 S3)) )))

[and_in:] (! (G:G) (P1:P) (P2:P) .
(clause_name "and_in") /\
(( ( spec_holds G P1 )) /\
( ( spec_holds G P2 )))
 ==> 
( ( spec_holds G (P_and P1 P2) )))

[and_el1:] (! (G:G) (P1:P) (P2:P) .
(clause_name "and_el1") /\
(( ( spec_holds G (P_and P1 P2) )))
 ==> 
( ( spec_holds G P1 )))

[and_el2:] (! (G:G) (P2:P) (P1:P) .
(clause_name "and_el2") /\
(( ( spec_holds G (P_and P1 P2) )))
 ==> 
( ( spec_holds G P2 )))

[imp_in:] (! (G:G) (P1:P) (P2:P) .
(clause_name "imp_in") /\
(( ( spec_holds  ( P1  INSERT  G )  P2 )))
 ==> 
( ( spec_holds G (P_implies P1 P2) )))

[imp_el:] (! (G:G) (P2:P) (P1:P) .
(clause_name "imp_el") /\
(( ( spec_holds G (P_implies P1 P2) )) /\
( ( spec_holds G P1 )))
 ==> 
( ( spec_holds G P2 )))

[or_in1:] (! (G:G) (P1:P) (P2:P) .
(clause_name "or_in1") /\
(( ( spec_holds G P1 )))
 ==> 
( ( spec_holds G (P_or P1 P2) )))

[or_in2:] (! (G:G) (P1:P) (P2:P) .
(clause_name "or_in2") /\
(( ( spec_holds G P2 )))
 ==> 
( ( spec_holds G (P_or P1 P2) )))

[or_el:] (! (G:G) (P:P) (P1:P) (P2:P) .
(clause_name "or_el") /\
(( ( spec_holds G (P_or P1 P2) )) /\
( ( spec_holds  ( P1  INSERT  G )  P )) /\
( ( spec_holds  ( P2  INSERT  G )  P )))
 ==> 
( ( spec_holds G P )))

[not_in:] (! (G:G) (P1:P) (P2:P) .
(clause_name "not_in") /\
(( ( spec_holds  ( P1  INSERT  G )  P2 )) /\
( ( spec_holds  ( P1  INSERT  G )  (P_not P2) )))
 ==> 
( ( spec_holds G (P_not P1) )))

[not_el:] (! (G:G) (P:P) .
(clause_name "not_el") /\
(( ( spec_holds G (P_not (P_not P)) )))
 ==> 
( ( spec_holds G P )))
End

val _ = export_theory ();
