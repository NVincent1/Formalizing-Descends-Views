
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