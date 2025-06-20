
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

Fixpoint ViewArray (l : nat) (d : List nat) :=
  match d with
  | [] => Idx l (* Index in the underlying array (s is the size of the array) *)
  | h::tl => Idx h -> (ViewArray l tl)
end.

Notation "[[ T ; n ]]" := (n::T).
Notation "[[ ; n ]]" := (n::[]).

Definition identity_view (n : nat) : ViewArray n [[;n]] :=
(* View resulting from applying `to_view` on an array :
  i-th element of the view is the i-th element of the array *)
  fun i => idx n (to_nat i) (BoundedInt n i).

Definition reverse {l : nat} {T : List nat} {n : nat} (v : ViewArray l [[T;n]]) : ViewArray l [[T;n]] :=
  fun i => v (idx n (n - 1 - to_nat i) reverseProof).

Definition take_left {l : nat} {T : List nat} {n : nat} (b : nat) (v : ViewArray l [[T;b+n]]) : ViewArray l [[T;b]] :=
  fun i => v (idx (b+n) (to_nat i) takeleftProof).

Definition take_right {l : nat} {T : List nat} {n : nat} (a : nat) (v : ViewArray l [[T;a+n]]) : ViewArray l [[T;n]] :=
  fun i => v (idx (a+n) (a + to_nat i) takerightProof).

Definition transpose {l : nat} {T : List nat} {n : nat} {m : nat} (v : ViewArray l [[ [[T;m]];n ]]) : ViewArray l [[ [[T;n]];m ]] :=
  fun i j => v j i.

Definition group {l : nat} {T : List nat} {n : nat} (m : nat) (v : ViewArray l [[T;m*n]]) : ViewArray l [[ [[T;m]];n]] :=
  fun i j => v (idx (m*n) (to_nat j + m*(to_nat i)) groupProof).

Definition map {l : nat} {A : List nat} {B : List nat} {n : nat} (f : ViewArray l A -> ViewArray l B) (v : ViewArray l [[A;n]]) : ViewArray l [[B;n]] :=
  fun i => f (v i).

