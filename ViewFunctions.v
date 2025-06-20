
From Views Require Import BoundedInt.
Require Import PeanoNat.



Inductive List (T : Type) : Type :=
  | Nil : List T
  | Cons (h : T) (tl : List T) : List T
.

Notation "h :: tl" := (Cons _ h tl).
Notation "[]" := (Nil _).

Fixpoint Tuple (d : List nat) : Type :=
  match d with
  | [] => True
  | h::tl => (Idx h) * (Tuple tl)
end.

Fixpoint ViewArray (s : nat) (d : List nat) :=
  match d with
  | [] => Idx s (* Index in the underlying array (s is the size of the array) *)
  | h::tl => Idx h -> (ViewArray s tl)
end.

Notation "[[ T ; n ]]" := (n::T).
Notation "[[ ; n ]]" := (n::[]).

Definition identity_view (n : nat) : ViewArray n [[;n]] :=
(* View resulting from applying `to_view` on an array :
  i-th element of the view is the i-th element of the array *)
  fun i => idx n (to_nat i) (BoundedInt n i).

Definition reverse {s : nat} {T : List nat} {n : nat} (v : ViewArray s [[T;n]]) : ViewArray s [[T;n]] :=
  fun i => v (idx n (n - 1 - to_nat i) reverseProof).

Definition take_left {s : nat} {T : List nat} {n : nat} (b : nat) (v : ViewArray s [[T;b+n]]) : ViewArray s [[T;b]] :=
  fun i => v (idx (b+n) (to_nat i) takeleftProof).

Definition take_right {s : nat} {T : List nat} {n : nat} (a : nat) (v : ViewArray s [[T;a+n]]) : ViewArray s [[T;n]] :=
  fun i => v (idx (a+n) (a + to_nat i) takerightProof).

Definition transpose {s : nat} {T : List nat} {n : nat} {m : nat} (v : ViewArray s [[ [[T;m]];n ]]) : ViewArray s [[ [[T;n]];m ]] :=
  fun i j => v j i.

Definition group {s : nat} {T : List nat} {n : nat} (m : nat) (v : ViewArray s [[T;m*n]]) : ViewArray s [[ [[T;m]];n]] :=
  fun i j => v (idx (m*n) (to_nat j + m*(to_nat i)) groupProof).

Definition map {s : nat} {A : List nat} {B : List nat} {n : nat} (f : ViewArray s A -> ViewArray s B) (v : ViewArray s [[A;n]]) : ViewArray s [[B;n]] :=
  fun i => f (v i).

