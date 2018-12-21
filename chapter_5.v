Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.

(* Theorem 54 *)
Theorem theorem_54 :
  forall k m d : Z, Zis_gcd k m d ->
                    forall a a' : Z, k*a mod m = k*a' mod m -> a mod (m/d) = a' mod (m/d).
Proof.
  intros.
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

