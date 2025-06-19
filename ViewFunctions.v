
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

Fixpoint ViewArray (d : List nat) :=
  match d with
  | [] => nat (* Index in the underlying array (could be changed into a Idx (bounded integer) with size given as a parameter) *)
  | h::tl => Idx h -> (ViewArray tl)
end.

Notation "[[ T ; n ]]" := (n::T).
Notation "[[ ; n ]]" := (n::[]).

(** TODO : change this function name *)
Definition to_view (n : nat) : ViewArray[[;n]] :=
  fun i => to_nat i.

Definition reverse {T : List nat} {n : nat} (v : ViewArray[[T;n]]) : ViewArray[[T;n]] :=
  fun i => v (idx n (n - 1 - to_nat i) reverseProof).

Definition take_left {T : List nat} {n : nat} (b : nat) (v : ViewArray[[T;b+n]]) : ViewArray[[T;b]] :=
  fun i => v (idx (b+n) (to_nat i) takeleftProof).

Definition take_right {T : List nat} {n : nat} (a : nat) (v : ViewArray[[T;a+n]]) : ViewArray[[T;n-a]] :=
  fun i => v (idx (a+n) (a + to_nat i) takerightProof).

Definition transpose {T : List nat} {n : nat} {m : nat} (v : ViewArray[[ [[T;m]];n ]]) : ViewArray[[ [[T;n]];m ]] :=
  fun i j => v j i.

Definition group {T : List nat} {n : nat} (m : nat) (v : ViewArray[[T;m*n]]) : ViewArray[[ [[T;m]];n]] :=
  fun i j => v (idx (m*n) (to_nat j + m*(to_nat i)) groupProof).

Definition map {A : List nat} {B : List nat} {n : nat} (f : ViewArray A -> ViewArray B) (v : ViewArray[[A;n]]) : ViewArray[[B;n]] :=
  fun i => f (v i).

