Require Import PeanoNat.

Lemma sub_neq :
  forall a b x, x > a ->  a - b = x -> False.
Proof.
  intros.
  assert ((a - b) <= a).
  apply Nat.le_sub_l.
  rewrite H0 in H1.
  apply Nat.nle_gt in H1. apply H1. apply H.
Qed.

Lemma sub_S :
  forall c a b, S c - a = S c - b -> c - a = c - b.
Proof.
  induction c.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct a; destruct b.
    + reflexivity.
    + exfalso. symmetry in H. rewrite Nat.sub_succ in H. apply sub_neq in H. apply H. apply le_n.
    + exfalso. rewrite Nat.sub_succ in H. apply sub_neq in H. apply H. apply le_n.
    + rewrite Nat.sub_succ in H. rewrite Nat.sub_succ in H.  apply IHc in H. apply H.
Qed.

Lemma sub_injective :
  forall c a b, a <= c -> b <= c -> c - a = c - b -> a = b.
Proof.
  induction c.
  - intros. inversion H. inversion H0. reflexivity.
  - intros. inversion H; subst.
    + rewrite Nat.sub_diag in H1. symmetry in H1. apply Nat.sub_0_le in H1. 
    apply Nat.le_antisymm. apply H1. apply H0. 
    + apply IHc with (a := a) (b := b) in H3. apply H3.
      inversion H0; subst. exfalso. rewrite Nat.sub_diag in H1. apply Nat.sub_0_le in H1.
      assert (a = S c). apply Nat.le_antisymm. apply H. apply H1. subst. apply Nat.lt_neq in H3. apply H3. 
      reflexivity. apply H4. apply sub_S in H1. apply H1.
Qed.

Definition add_injective := Nat.add_cancel_l.

Lemma eq_mod :
  forall a b c, a = b -> a mod c = b mod c.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma mod_red :
  forall c a b, (a + c*b) mod c = a mod c.
Proof.
  intros. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma projection_injective :
  forall k a b x y, a < k -> x < k -> a + k*b = x + k*y -> (a,b) = (x,y).
Proof.
  intros. assert (a = x). apply eq_mod with (c := k) in H1. rewrite mod_red in H1. rewrite mod_red in H1.
    rewrite Nat.mod_small in H1. symmetry in H1. rewrite Nat.mod_small in H1. symmetry. apply H1.
    apply H0. apply H. subst. apply add_injective in H1. apply Nat.mul_cancel_l in H1. subst. reflexivity.
    destruct k. inversion H0. intro. inversion H3.
Qed.

