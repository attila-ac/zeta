(* Import necessary libraries *)
Require Import ZArith.
Require Import Reals.
From Formalization Require Import define_complex.

(* Open the real number scope *)
Open Scope R_scope.

(* Define the Hadamard term for poles *)
Definition hadamard_term_pole (z rho : C) : C :=
  Cdiv (mkC 1 0) (Csub z rho).

(* Example test case for hadamard_term_pole *)
Definition test_hadamard_term_pole : C :=
  hadamard_term_pole (mkC 1 1) (mkC 2 3).

