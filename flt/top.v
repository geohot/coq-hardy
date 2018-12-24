From mathcomp Require Import all_ssreflect.
Require Import Coq.omega.Omega.

(* see http://www.cs.rug.nl/~wim/fermat/wilesEnglish.html for proof sketch *)

Search (_ %| _).

Lemma gcdmultk k a b : gcdn (k*a) (k*b) == k -> gcdn a b == 1.
Proof. 
  move/eqP.
  

  intros.
  
  
  intros gk.
  apply/eqP/gcdn_def; try by [].
  intros.
  
Admitted.

Lemma coprime_gcd a b : coprime (a %/ (gcdn a b)) (b %/ (gcdn a b)).
Proof.
  unfold coprime.
  apply (gcdmultk (gcdn a b)).
  
  
  

  
  
  
  
  apply/eqP.
  apply gcdn_def; try by [].
  intros.
  
  
  intros d'.
  
  move=> /dvdnP.
  intros ek.
  destruct ek.
  
  move=> /dvdnP.
  intros el.
  destruct ek.
  destruct el.
  
  
  
  intros.

  case/dvdnP=> n'.
  
  rewrite/dvdnP in H.
  

  
  apply coprime_dvdl with (n:=a).
  unfold coprime.
  
  assert (gabda : gcdn a b %| a).
  apply dvdn_gcdl.

  assert (gabdb : gcdn a b %| b).
  apply dvdn_gcdr.

  apply/eqP.
  
  apply gcdn_def; try by [].
  intros.
  
  

 
  admit.

  
  



  
  intros.
  
  
Admitted.

Search ((_ %/ _) ^ _).


Theorem theorem_1 : forall n, (exists x y z, x^n + y^n = z^n) -> (exists a b c, a^n + b^n = c^n /\ (coprime a b)).
Proof.
  intros n [x [y [z H]]].
  pose (d := gcdn x y).

  (* assert (ddivx : d %| x). *)
  
  exists (x %/ d).
  exists (y %/ d).
  exists (z %/ d).
  split.
  
  2 : {
    unfold d.
    apply coprime_gcd.
  }
  


  
  
  
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
    (* ugh ssreflect is annoying *)
    rewrite ltn_neqAle ltn_neqAle.
    case and3P.
    intros; by [].
    intros.
    destruct n0.
    split.
    apply/eqnP; auto.
    apply/eqnP; auto.
    assumption.
  }
  clear ngt nn4 nn3.

  specialize (theorem_4).
  intros.
  destruct H.
  exists a, b, c, n.
  split; assumption.
  clear a b c n eq ngt4.
  rename x into a.
  destruct H as [b [c [n [ngt [pn eq]]]]].

  specialize (theorem_1 n).
  intros.
  destruct H.
  exists a,b,c.
  assumption.
  clear a b c eq.
  rename x into a.
  destruct H as [b [c [eq coab]]].

  (* and here some stuff about elliptic curves *)
Abort.


