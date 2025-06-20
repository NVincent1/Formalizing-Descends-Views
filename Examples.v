
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
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
            | (idx _ 0 _,idx _ 0 _) => idx 6 2 H2'
            | (idx _ 0 _,idx _ 1 _) => idx 6 1 H1'
            | (idx _ 0 _,idx _ 2 _) => idx 6 0 H0'
            | (idx _ 1 _,idx _ 0 _) => idx 6 5 H5'
            | (idx _ 1 _,idx _ 1 _) => idx 6 4 H4'
            | (idx _ 1 _,idx _ 2 _) => idx 6 3 H3'
            | _ => idx 6 0 H0'
end).
Proof.
  simpl. unfold map. unfold identity_view. unfold group. unfold reverse. 
  apply FunEquality. intros. apply FunEquality. intro y. destruct x as [x Hx]. destruct y as [y Hy]. destruct x.
  - simpl. destruct y. apply unif_Idx. destruct y. apply unif_Idx. destruct y. apply unif_Idx. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  - destruct x.
    + simpl. destruct y. apply unif_Idx. destruct y. apply unif_Idx. destruct y. apply unif_Idx. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
    + exfalso. inversion Hx. inversion H0. inversion H2.
Qed.

Lemma inf : forall s n (i : Idx n),
  s >= n -> to_nat i < s.
Proof.
  intros.
  apply Nat.le_trans with (m := n).
  apply BoundedInt. apply H.
Qed.

Definition index_identity {s : nat} {T : List nat} {n : nat} (H : s >= n) (v : ViewArray s [[T;n]]) : ViewArray s [[;n]] :=
  fun i => idx s (to_nat i) (inf s n i H).

Example index_identity_does_not_preserve_injectivity :
  (forall s T n (H : s >= n), preserve_Injectivity (index_identity H) (s := s) (A := (n::T))) -> False.
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
  assert ((2*2) >= 2). simpl. auto.
  apply H with (v := (group 2 (identity_view (2*2)))) (H := H3) (C := (2::[]))
      (i := (idx 2 1 H1,I))
      (x := (idx 2 0 H0,I))
      (j := (idx 2 0 H0,I))
      (y := (idx 2 0 H0,I))
  . apply H2. simpl. reflexivity.
  inversion H3.
Qed.