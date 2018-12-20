Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.

Check Z.pow_pos.
Search (0 ^ _).

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

(* Theorem 71 *)
Theorem fermats_theorem : forall a p : Z, prime p /\ ~(p|a) -> a^(p-1) mod p = 1.
Proof.
Abort.

(* Theorem 72 : a^phi(m) mod m = 1 *)


