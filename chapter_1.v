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

(* Theorem 4: The number of primes is infinite *)
(*    have a coq proof for this, but it's long and ugly, clean it up first *)
Theorem infinite_primes: forall n : Z, exists p : Z, p > n /\ prime p.
Proof.
Abort.

(* Theorem 5: Consecutive composites of arbitrary length exist *)
Theorem theorem_5: forall n : Z, exists c : Z, forall x : Z, c <= x < c+n -> ~(prime x).
Proof.
Abort.

(* heh *)
Theorem twin_prime_conjecture: forall n : Z, exists p : Z, p > n /\ prime p /\ prime (p+2).
Proof.
Abort.

(* Theorem 6: The prime number theorem pi(x) ~ x/(log x) *)
(*   Hmm, well they don't prove this is chapter 1... *)
(* Theorems 7,8,9 are similar *)

