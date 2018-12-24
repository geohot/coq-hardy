From mathcomp Require Import all_ssreflect.
Require Import Coq.omega.Omega.

(* see http://www.cs.rug.nl/~wim/fermat/wilesEnglish.html for proof sketch *)

Theorem theorem_1 : exists n, (exists a b c, a^n + b^n = c^n) -> (exists a b c, a^n + b^n = c^n /\ (coprime a b)).
Proof.
Admitted.

Theorem theorem_2 : forall a b c, a^4 + b^4 <> c^4.
Proof.
Admitted.

Theorem theorem_3 : forall a b c, a^3 + b^3 <> c^3.
Proof.
Admitted.

Theorem theorem_4 : (exists a b c n, n > 4 /\ a^n + b^n = c^n) ->
                                    (exists a b c n, n > 4 /\ prime n /\ a^n + b^n = c^n).
Proof.
  simpl.
Admitted.

Theorem fermats_last_theorem : ~exists a b c n, a^n + b^n = c^n /\ n > 2.
Proof.
  red.
  intros [a [b [c [n [eq ngt]]]]].
  assert (nn4 : n <> 4). {
    specialize (theorem_2 a b c).
    red; intros; rewrite H0 in eq; rewrite eq in H; contradiction.
  }
  assert (nn3 : n <> 3). {
    specialize (theorem_3 a b c).
    red; intros; rewrite H0 in eq; rewrite eq in H; contradiction.
  }
  assert (ngt4 : n > 4). {
    admit.
  }
  clear ngt nn4 nn3.

  specialize (theorem_4).
  intros.
  destruct H.
  exists a, b, c, n.
  split; assumption.
  clear a b c n eq ngt4.
  rename x into a.
  destruct H as [b [c [n [eq [pn ngt]]]]].
Abort.
  