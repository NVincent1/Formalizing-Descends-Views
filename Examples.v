
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
From Views Require Import ViewsLemmas.
Require Import PeanoNat.

Axiom FunEquality :
  forall A B (f : A -> B) (g : A -> B),
  f = g <-> forall x, f x = g x.

Definition H0' : 0 < 6.
Proof. apply le_n_S. apply le_0_n. Qed.
Definition H1' : 1 < 6.
Proof. repeat apply le_n_S. apply le_0_n. Qed.
Definition H2' : 2 < 6.
Proof. auto. Qed.
Definition H3' : 3 < 6.
Proof. auto. Qed.
Definition H4' : 4 < 6.
Proof. auto. Qed.
Definition H5' : 5 < 6.
Proof. auto. Qed.

Example testmap :
  (map reverse (group 3 (identity_view (3*2)))) = 
  (fun x y => match (x,y) with 
            | (idx _ 0 _,idx _ 0 _) => 2
            | (idx _ 0 _,idx _ 1 _) => 1
            | (idx _ 0 _,idx _ 2 _) => 0
            | (idx _ 1 _,idx _ 0 _) => 5
            | (idx _ 1 _,idx _ 1 _) => 4
            | (idx _ 1 _,idx _ 2 _) => 3
            | _ => 0
end).
Proof.
  simpl. unfold map. unfold identity_view. unfold group. unfold reverse. 
  apply FunEquality. intros. apply FunEquality. intro y. destruct x as [x Hx]. destruct y as [y Hy]. destruct x.
  - simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  - destruct x.
    + simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
    + exfalso. inversion Hx. inversion H0. inversion H2.
Qed.

Lemma inf : forall s n (i : Idx n),
  s >= n -> to_nat i < s.
Proof.
  intros.
  apply Nat.le_trans with (m := n).
  apply BoundedInt. apply H.
Qed.

Definition index_identity {T : List nat} {n : nat} (v : ViewArray [[T;n]]) : ViewArray [[;n]] :=
  fun i => to_nat i.

Example index_identity_does_not_preserve_injectivity :
  (forall T n, preserve_Injectivity index_identity (A := (n::T))) -> False.
Proof.
  intros.
  unfold preserve_Injectivity in H.
  assert (0 < 2). apply le_n_S. apply le_0_n.
  assert (1 < 2). apply le_n_S. apply le_n.
  assert (Injective (group 2 (identity_view (2*2)))).
    assert (Injective (identity_view (2*2)) -> Injective (group 2 (identity_view (2 * 2)))).
    apply preserve_Injectivity_implies_preserving_view_injectivity. apply group_preserves_injectivity.
    apply H2. apply identity_view_injective.
  assert (((idx 2 1 H1,I), (idx 2 0 H0,I)) = ((idx 2 0 H0,I), (idx 2 0 H0,I))).
  apply H with (v := (group 2 (identity_view (2*2)))) (C := (2::[]))
      (i := (idx 2 1 H1,I))
      (x := (idx 2 0 H0,I))
      (j := (idx 2 0 H0,I))
      (y := (idx 2 0 H0,I))
  . apply H2. simpl. reflexivity.
  inversion H3.
Qed.