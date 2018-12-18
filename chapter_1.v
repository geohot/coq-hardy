Require Export ZArith.
Require Export Znumtheory.
Require Import Classical.

(* Theorem 1: Every positive integer, except 1, is a product of primes *)

(* Theorem 2: Fundamental theorem of arithmetic *)

(* Theorem 3 *)
Theorem euclids_first_theorem :
  forall p : Z, prime p ->
                forall a b : Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intros p prime_p a b div.

  elim (classic (p | a)).
  intros. left. assumption.
  intros. right.

  specialize (prime_rel_prime p).
  intros.
  apply H0 with (a:=a) in prime_p; [|assumption].

  specialize (Gauss p a b).
  intros.
  auto.
Qed.



                                    