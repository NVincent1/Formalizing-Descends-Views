
From Views Require Import BoundedInt.
From Views Require Import ViewsProof.

Example testmap :
  (map reverse (group 3 2 (to_view 6))) = 
  (fun x => match x with 
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
  apply FunEquality. intros. destruct x. destruct t. destruct i. simpl. destruct n0.
  - simpl. destruct n. reflexivity. simpl. destruct n. reflexivity. destruct n. reflexivity. exfalso. inversion H. inversion H2. inversion H4. inversion H6.
  - destruct n0.
    + simpl. destruct n. reflexivity. simpl. destruct n. reflexivity. destruct n. reflexivity. exfalso. inversion H. inversion H2. inversion H4. inversion H6.
    + exfalso. inversion H0. inversion H2. inversion H4.
Qed.