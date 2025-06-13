
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
Require Import PeanoNat.

Axiom FunEquality :
  forall A B (f : A -> B) (g : A -> B),
  f = g <-> forall x, f x = g x.

Example testmap :
  (map reverse (group 3 (to_view (3*2)))) = 
  (fun x y => match (x,y) with 
            | (Id _ 0 _,Id _ 0 _) => 2
            | (Id _ 0 _,Id _ 1 _) => 1
            | (Id _ 0 _,Id _ 2 _) => 0
            | (Id _ 1 _,Id _ 0 _) => 5
            | (Id _ 1 _,Id _ 1 _) => 4
            | (Id _ 1 _,Id _ 2 _) => 3
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


