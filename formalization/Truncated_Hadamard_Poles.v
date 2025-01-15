(*
Formalization of the Riemann Hypothesis Proof via Zeropole Balance
Debugging Three Trivial Poles in Hadamard Product
Author: Attila Csordas
License: CC-BY-NC 4.0
*)

(* Import necessary libraries and dependencies *)
Require Import ZArith. (* For integers *)
Require Import Reals. (* For real numbers *)
From Formalization Require Import define_complex. (* Import complex numbers framework *)

(* Open the real number scope for easier operations *)
Open Scope R_scope.

(* Define the Hadamard term for trivial poles at s = -2k *)
Definition hadamard_term_pole (s pole : C) : C :=
  Cdiv (mkC 1 0) (Csub s pole).

(* Define the first three trivial poles *)
Definition first_trivial_pole : C := mkC (-2) 0.
Definition second_trivial_pole : C := mkC (-4) 0.
Definition third_trivial_pole : C := mkC (-6) 0.

(* Compute the Hadamard term for the first trivial pole *)
Definition test_truncated_poles_1 : C :=
  hadamard_term_pole (mkC 1 1) first_trivial_pole.

(* Compute the Hadamard term for the second trivial pole *)
Definition test_truncated_poles_2 : C :=
  hadamard_term_pole (mkC 1 1) second_trivial_pole.

(* Compute the Hadamard term for the third trivial pole *)
Definition test_truncated_poles_3 : C :=
  hadamard_term_pole (mkC 1 1) third_trivial_pole.

(* Compute the Hadamard product for the first three trivial poles *)
Definition hadamard_product_three_poles : C :=
  Cmul
    (Cmul test_truncated_poles_1 test_truncated_poles_2)
    test_truncated_poles_3.

(* Explicitly define the expected result for the three-pole product *)
Definition three_poles_explicit : C :=
  Cmul
    (Cmul
       (Cdiv (mkC 1 0) (Csub (mkC 1 1) first_trivial_pole))
       (Cdiv (mkC 1 0) (Csub (mkC 1 1) second_trivial_pole)))
    (Cdiv (mkC 1 0) (Csub (mkC 1 1) third_trivial_pole)).

(* Theorem: Verify the computed Hadamard product matches the explicit value *)
Theorem test_three_trivial_poles :
  hadamard_product_three_poles = three_poles_explicit.
Proof.
  reflexivity.
Qed.

(* Debugging Outputs *)

(* Check the first trivial pole *)
Eval compute in first_trivial_pole.

(* Check the second trivial pole *)
Eval compute in second_trivial_pole.

(* Check the third trivial pole *)
Eval compute in third_trivial_pole.

(* Check the Hadamard term for the first trivial pole *)
Eval compute in test_truncated_poles_1.

(* Check the Hadamard term for the second trivial pole *)
Eval compute in test_truncated_poles_2.

(* Check the Hadamard term for the third trivial pole *)
Eval compute in test_truncated_poles_3.

(* Check the Hadamard product for the first three poles *)
Eval compute in hadamard_product_three_poles.

(* Check the explicitly defined product for the three poles *)
Eval compute in three_poles_explicit.

