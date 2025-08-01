
From Views Require Import BoundedInt.
From Views Require Import utils.
Require Import PeanoNat.


Fixpoint ViewArray (d : List nat) :=
  match d with
  | [] => nat (* Index in the underlying array *)
  | h::tl => Idx h -> (ViewArray tl)
end.

Notation "[[ T ; n ]]" := (n::T).
Notation "[[ ; n ]]" := (n::[]).

Definition identity_view (n : nat) : ViewArray [[;n]] :=
(* View resulting from applying `to_view` on an array :
  i-th element of the view is the i-th element of the array *)
  fun i => to_nat i.

Definition reverse {T : List nat} {n : nat} : Tuple (n::T) -> Tuple (n::T) :=
  fun i => match i with | (i,x) => (idx n (n - 1 - to_nat i) reverseBounded,x) end.

Definition take_left {T : List nat} {n : nat} (b : nat) : Tuple (b::T) -> Tuple(b+n::T) :=
  fun i => match i with | (i,x) => (idx (b+n) (to_nat i) takeleftBounded,x) end.

Definition take_right {T : List nat} {n : nat} (a : nat) : Tuple (n::T) -> Tuple (a+n::T) :=
  fun i => match i with | (i,x) => (idx (a+n) (a + to_nat i) takerightBounded,x) end.

Definition select_range {T : List nat} {n : nat} (a : nat) (b : nat) : Tuple (b-a::T) -> Tuple (b+n::T) :=
  fun i => match i with | (i,x) => (idx (b+n) (a + to_nat i) selectrangeBounded,x) end.

Definition transpose {T : List nat} {n : nat} {m : nat} : Tuple (m::n::T) -> Tuple (n::m::T) :=
  fun i => match i with | (i,(j,x)) => (j,(i,x)) end.

(* m is the size of the groups *)
Definition group {T : List nat} {n : nat} (m : nat) : Tuple (n::m::T) -> Tuple (m*n::T) :=
  fun i => match i with | (i,(j,x)) => (idx (m*n) (to_nat j + m*(to_nat i)) groupBounded,x) end.

Definition map {A : List nat} {B : List nat} {n : nat} (f : ViewArray A -> ViewArray B) (v : ViewArray [[A;n]]) : ViewArray [[B;n]] :=
  fun i => f (v i).


(* flatten view, inverse of the group view *)
Definition flatten {T : List nat} {n : nat} (m : nat) : Tuple (m*n::T) -> Tuple (n::m::T) :=
    fun i => match i with | (i,x) => (idx n (to_nat i / m) flattenBounded2,(idx m (to_nat i mod m) flattenBounded1,x)) end.

