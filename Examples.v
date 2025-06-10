
From Views Require Import BoundedInt.
From Views Require Import ViewsProof.
Require Import PeanoNat.

Example testmap :
  (map reverse (group 3 2 (to_view 6))) = 
  (fun x => match x with 
            | (Id _ 0 _,(Id _ 0 _,I)) => 2
            | (Id _ 0 _,(Id _ 1 _,I)) => 1
            | (Id _ 0 _,(Id _ 2 _,I)) => 0
            | (Id _ 1 _,(Id _ 0 _,I)) => 5
            | (Id _ 1 _,(Id _ 1 _,I)) => 4
            | (Id _ 1 _,(Id _ 2 _,I)) => 3
            | _ => 0
end).
Proof.
  simpl. unfold map. unfold to_view. unfold group. unfold reverse. 
  apply FunEquality. intros. destruct x. destruct t. destruct i. destruct i0. destruct t. unfold partialApp. destruct n0.
  - simpl. destruct n. reflexivity. simpl. destruct n. simpl. reflexivity. exfalso. inversion H. inversion H2. inversion H4.
  - destruct n0.
    + simpl. destruct n. reflexivity. simpl. destruct n. reflexivity. exfalso. inversion H. inversion H2. inversion H4.
    + destruct n0.
      * simpl. destruct n. simpl. reflexivity. simpl. destruct n. reflexivity. exfalso. inversion H. inversion H2. inversion H4.
      * exfalso. inversion H0. inversion H2. inversion H4. inversion H6.
Qed.


Definition f_annoying {n : nat} (v : ViewArray [[;n]]) : ViewArray [[; n]] :=
  fun (i : Tuple (n::[])) =>
      match i with | (i,j) =>
      (to_nat i)
  end
.

Example annoying :
  map (f_annoying) (group 2 2 (to_view 4)) = 
  fun (x : Tuple (2::2::[])) =>
    match x with
    | (Id _ 0 _,(Id _ 0 _,I)) => 0
    | (Id _ 0 _,(Id _ 1 _,I)) => 1
    | (Id _ 1 _,(Id _ 0 _,I)) => 0
    | (Id _ 1 _,(Id _ 1 _,I)) => 1
    | _ => 0
end.
Proof.
  unfold map. unfold f_annoying. unfold partialApp. simpl. apply FunEquality.
  intros. destruct x. destruct t. destruct t.
  destruct i0,i.
  destruct n;destruct n0.
    + simpl. reflexivity.
    + simpl. destruct n0. reflexivity. exfalso. inversion H0. inversion H2. inversion H4.
    + simpl. destruct n. reflexivity. exfalso. inversion H. inversion H2. inversion H4.
    + simpl. destruct n; destruct n0. reflexivity.
    exfalso. inversion H0. inversion H2. inversion H4.
    exfalso. inversion H. inversion H2. inversion H4.
    exfalso. inversion H. inversion H2. inversion H4.
Qed.

Example annoying_is_injective :
  forall (n : nat) (v : ViewArray [[;n]]) (i : Idx n) (j : Idx n), (f_annoying v) (i,I) = (f_annoying v) (j,I) -> i = j.
Proof.
  intros.
  unfold f_annoying in *.
  apply to_nat_injective in H. apply H.
Qed.
