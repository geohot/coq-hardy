Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.

(* Theorem 54 *)
Lemma mod_sub_ish : forall a b m : Z, a mod m = b mod m -> (a - b) mod m = 0.
Proof.
  intros.
Admitted.           

Theorem theorem_54 :
  forall k m d : Z, Zis_gcd k m d ->
                    forall a a' : Z, k*a mod m = k*a' mod m -> a mod (m/d) = a' mod (m/d).
Proof.
  intros.
  induction H.
  destruct H as [k1 H].
  destruct H1 as [m1 H1].

  assert (rel_prime k1 m1).
  constructor.
  exists k1; omega.
  exists m1; omega.
  intros.
  admit.  

  
Admitted.

(* Theorem 55 *)
Theorem theorem_55 :
  forall k m : Z, rel_prime k m ->
               forall a a' : Z, k*a mod m = k*a' mod m -> a mod m = a' mod m.
Proof.
  intros.
  specialize (theorem_54 k m 1).
  intros.
  unfold rel_prime in H.
  apply H1 with (a:=a) (a':=a') in H.
  rewrite -> Zdiv_1_r in H.
  apply H.
  apply H0.
Qed.

