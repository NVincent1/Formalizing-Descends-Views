
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
Require Import PeanoNat.

Axiom FunEquality :
  forall A B (f : A -> B) (g : A -> B),
  f = g <-> forall x, f x = g x.

Example testmap :
  (map reverse (group 3 (to_view (3*2)))) = 
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
  simpl. unfold map. unfold to_view. unfold group. unfold reverse. 
  apply FunEquality. intros. apply FunEquality. intro y. destruct x as [x Hx]. destruct y as [y Hy]. destruct x.
  - simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  - destruct x.
    + simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
    + exfalso. inversion Hx. inversion H0. inversion H2.
Qed.


Definition identity {T : List nat} {n : nat} (v : ViewArray[[T;n]]) : ViewArray[[;n]] :=
  fun i => to_nat i.

Example ok :
  (forall T n, curry_Injective (identity) (A := (n::T))) -> False.
Proof.
  intros.
  unfold curry_Injective in H.
  assert (0 < 2). apply le_n_S. apply le_0_n.
  assert (1 < 2). apply le_n_S. apply le_n.
  assert (Injective (group 2 (to_view (2*2)))).
    assert (Injective (to_view (2*2)) -> Injective (group 2 (to_view (2 * 2)))).
    apply curry_Injective_implies_preserving_injectivity. apply group_preserves_injectivity.
    apply H2. apply to_view_injective.
  destruct (H [] 2 (2::[]) (group 2 (to_view (2*2))) H2 (idx 2 0 H0,I) (idx 2 1 H1,I) (idx 2 0 H0,I) (idx 2 0 H0,I)).
  unfold group. simpl. reflexivity.
  inversion H3.
Qed.
