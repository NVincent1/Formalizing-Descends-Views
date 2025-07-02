
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

Fixpoint map {A : Type} {B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | [] => []
  | h :: tl => (f h) :: map f tl
end.

Fixpoint cat {T : Type} (l1 : List T) (l2 : List T) : List T :=
  match l1 with
  | [] => l2
  | h::tl => h::(cat tl l2)
end.

Notation "l1 ++ l2" := (cat l1 l2).

Fixpoint zip {T : Type} (l : List (List T)) : List T :=
  match l with
  | [] => []
  | h::tl => h ++ (zip tl)
end.

Definition cropBounded {n : nat} {i : Idx n} :
  to_nat i < S n.
Proof.
  apply le_S. apply BoundedInt.
Qed.

Definition crop {T : Type} {n : nat} (f : Idx (S n) -> T) : Idx n -> T :=
  fun i => f (idx (S n) (to_nat i) cropBounded)
.

Fixpoint buildList {T : Type} {n : nat} : (Idx n -> T) -> List T :=
  match n with
  | 0 => fun f => []
  | S n => fun f => (f maxIdx)::(buildList (crop f))
end.

Fixpoint rev {T : Type} (l : List T) :=
  match l with
  | [] => []
  | h :: tl => (rev tl) ++ (h :: [])
end.


