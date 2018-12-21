Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.
(*Require Export Binomial.
Require Export Rdefinitions.*)

Definition nCr n r : Z := Z.of_nat ((fact n) / (fact r * fact (n-r))).

(*Search ((_:nat -> Z) (_:nat)).*)

Fixpoint sum_fZ (f:nat -> Z) (n:nat): Z :=
  match n with
  | O => f 0%nat
  | S i => sum_fZ f i + f (S i)
  end.

Lemma zbinomial : forall (x y n:Z),
    (x + y) ^ n = sum_fZ (fun i:nat => nCr (Z.to_nat n) i * x ^ (Z.of_nat i) * y ^ (Z.of_nat ((Z.to_nat n)-i))) (Z.to_nat n).
Proof.
Admitted.

(* Theorem 70 *)

Lemma freshmans_dream : forall p : Z, prime p -> forall x y : Z, (x + y)^p mod p = (x^p+y^p) mod p.
Proof.
Admitted.

Theorem theorem_70 : forall p : Z, prime p -> forall a : Z, a>=0 -> a^p mod p = a mod p.
Proof.
  intros.
  pattern a.
  apply natlike_ind.
  rewrite Z.pow_0_l.
  reflexivity.
  apply prime_ge_2 in H.
  omega.

  intros.
  replace (Z.succ x) with (x + 1); [|omega].
  rewrite freshmans_dream.
  replace (1^p) with 1.
  rewrite <- Zplus_mod_idemp_l.
  rewrite H2.
  rewrite -> Zplus_mod_idemp_l.
  reflexivity.

  symmetry.
  apply Z.pow_1_l.
  apply prime_ge_2 in H.
  omega.
  assumption.
  omega.
Qed.

Search (_ * _ = _ * _).

(* Theorem 71 *)
Lemma mod_mul_cancel_l : forall p q r n : Z, prime n /\ ~(n|r) -> (r * p) mod n = (r * q) mod n <-> p mod n = q mod n.
Proof.
  intros.
  split.
  
  intros eq.
  (* hmm, is this actually true, or only if n is prime... *)
  

  admit.

  intros eq.
  rewrite <- Zmult_mod_idemp_r.
  rewrite eq.
  rewrite -> Zmult_mod_idemp_r.
  reflexivity.
Admitted.                     

Theorem fermats_theorem : forall a p : Z, a>=0 -> prime p /\ ~(p|a) -> a^(p-1) mod p = 1.
Proof.
  intros a p age0 [H H0].

  (* so basically it comes down to the fact that a must have an inverse mod p *)

  (*
  replace (a ^ (p - 1) mod p = 1) with (p|(a ^ (p - 1) - 1)).
  unfold Z.divide.

  specialize (theorem_70 p).
  intros eq.
  apply eq with (a:=a) in H.
  clear eq.

  replace (a ^ p mod p = a mod p) with (p | (a ^ p - a)) in H.
  destruct H.
  exists x.
  rewrite <- (Z.mul_cancel_l _ _ a).
  *)

  replace 1 with (1 mod p) at 2.
  2 : {
    apply Zmod_small.
    apply prime_ge_2 in H.
    omega.
  }
  
  rewrite <- (mod_mul_cancel_l _ _ a).
  rewrite <- Z.pow_succ_r.
  replace (Z.succ (p - 1)) with p; [|omega].
  rewrite Z.mul_1_r.
  rewrite theorem_70.
  reflexivity.
  
  - apply H.
  - apply age0.
  - apply prime_ge_2 in H.
    omega.
  - split.
    + apply H.
    + apply H0.
Qed.

(* Theorem 72 : a^phi(m) mod m = 1 *)


