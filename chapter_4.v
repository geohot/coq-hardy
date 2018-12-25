Require Import Omega Wf_nat Even Classical_Pred_Type.

(* Theorem 43: sqrt(2) is irrational *)
Theorem sqrt2_irrational a b : a>0 -> a*a <> 2*b*b.
Proof.
  red.
  generalize b.
  pattern a.
  apply (well_founded_ind lt_wf).
  clear.
  intros a H b anz eq.

  assert (a2e : Nat.Even (a * a)).
  exists (b*b).
  rewrite -> Nat.mul_assoc.
  assumption.

  assert (ae : Nat.Even a).
  rewrite <- even_equiv.
  rewrite <- even_equiv in a2e.
  apply even_mult_aux in a2e.
  now destruct a2e.
  
  assert (bnz : b > 0).
  specialize (gt_0_eq b).
  intros [|]; [assumption|].
  rewrite <- H0 in eq.
  simpl in eq.
  apply Nat.eq_mul_0 in eq.
  destruct eq; omega.
 
  destruct ae as [x a2x].
  specialize (H b).
  destruct H with (b0 := x).
  - apply Nat.square_lt_simpl_nonneg; [omega|].
    rewrite -> eq.
    rewrite <- Nat.mul_assoc.
    rewrite <- (Nat.mul_1_l (b * b)) at 1.
    apply Nat.mul_lt_mono_pos_r; [|omega].
    apply Nat.mul_pos_pos; omega.
  - assumption.
  - rewrite a2x in eq.
    repeat rewrite <- Nat.mul_assoc in eq.
    rewrite -> Nat.mul_cancel_l in eq; auto.
    rewrite Nat.mul_comm in eq.
    symmetry.
    assumption.
Qed.

Search (_ * (_ / _)).

(* Theorem 46: log10(2) is irrational *)

Lemma fivex_2b x b : 5*x <> 2^b.
Proof. 
  generalize x.
  clear x.
  
  induction b.
  red.
  intros.
  simpl in H.
  omega.
  
  red.
  intros.
  assert (Nat.Even x).
  rewrite <- even_equiv.
  apply even_mult_inv_r with (n:=5).
  rewrite -> H.
  rewrite Nat.pow_succ_r.
  rewrite -> even_equiv.
  exists (2^b).
  reflexivity.
  omega.
  rewrite -> odd_equiv.
  exists 2.
  auto.

  destruct H0.
  specialize (IHb x0).
  destruct IHb.
  rewrite Nat.pow_succ_r in H; [|omega].

  rewrite <- (Nat.mul_cancel_l _ _ 2); [|omega].
  rewrite <- H.
  rewrite -> H0.
  repeat rewrite Nat.mul_assoc.
  auto.
Qed.

Search (S (pred _)).

Theorem log102_irrational a b : (a > 0) -> (2^b <> 10^a).
Proof.
  red.
  intros anz eq.

  assert (exists c, 5*c = 10^a).
  exists (2 * (10^(pred a))).
  rewrite Nat.mul_assoc.
  replace (5 * 2) with 10; [|omega].
  rewrite <- Nat.pow_succ_r; [|omega].
  rewrite <- S_pred_pos; [|omega].
  reflexivity.
  
  destruct H.
  rewrite <- eq in H.
  apply fivex_2b in H.
  assumption.
Qed.

(* Theorem 47: e is irrational *)


