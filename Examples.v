
From Views Require Import ViewsProof.

Example testmap :
  (map reverse (group 3 2 (to_view 6))) = 
  (fun x => match x with 
            | (0,0) => 1
            | (0,1) => 0
            | (1,0) => 3
            | (1,1) => 2
            | (2,0) => 5
            | (2,1) => 4
            | _ => 0
end).
Proof.
  simpl. unfold map. unfold partialapp. unfold to_view. unfold group. unfold reverse. 
  apply FunEquality. intros. destruct x. assert (i < 3). apply BoundedInt. assert (t < 2). apply BoundedInt. destruct i.
  - simpl. destruct t. reflexivity. simpl. destruct t. reflexivity. exfalso. inversion H0. inversion H2. inversion H4.
  - destruct i.
    + simpl. destruct t. reflexivity. destruct t. reflexivity. exfalso. inversion H0. inversion H2. inversion H4.
    + destruct i.
      * simpl. destruct t. reflexivity. destruct t. reflexivity. exfalso. inversion H0. inversion H2. inversion H4.
      * exfalso. inversion H. inversion H2. inversion H4. inversion H6.
Qed.