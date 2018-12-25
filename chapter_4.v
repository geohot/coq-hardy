Require Import Omega Wf_nat Even.

(* Theorem 43: sqrt(2) is irrational *)
Theorem sqrt2_irrational a b : a>0 -> a*a <> 2*b*b.
Proof.
  red.
  generalize b.

  elim a using (well_founded_ind lt_wf).
  clear.
  intros a H b anz eq.

  assert (Nat.Even (a * a)).
  exists (b*b).
  rewrite -> Nat.mul_assoc.
  assumption.

  assert (Nat.Even a).
  rewrite <- even_equiv.
  rewrite <- even_equiv in H0.
  apply even_mult_aux in H0.
  now destruct H0.
  
  assert (bnz : b > 0).
  specialize (gt_0_eq b).
  intros [|]; [assumption|].
  rewrite <- H2 in eq.
  simpl in eq.
  apply Nat.eq_mul_0 in eq.
  destruct eq; omega.
 
  destruct H1.
  specialize (H b).
  destruct H with (b0 := x).
  - symmetry in eq.
    apply Nat.square_lt_simpl_nonneg; [omega|].
    rewrite <- eq.
    rewrite <- Nat.mul_assoc.
    rewrite <- (Nat.mul_1_l (b * b)) at 1.
    apply Nat.mul_lt_mono_pos_r.
    apply Nat.mul_pos_pos; omega.
    omega.    
  - assumption.
  - rewrite H1 in eq.
    repeat rewrite <- Nat.mul_assoc in eq.
    rewrite -> Nat.mul_cancel_l in eq; auto.
    rewrite Nat.mul_comm in eq.
    rewrite eq.
    reflexivity.
Qed.


  
  
  