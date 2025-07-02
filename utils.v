
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

Definition cropleftBounded {n : nat} {i : Idx n} :
  S(to_nat i) < S n.
Proof.
  apply le_n_S. apply BoundedInt.
Qed.

Definition crop {T : Type} {n : nat} (f : Idx (S n) -> T) : Idx n -> T :=
  fun i => f (idx (S n) (to_nat i) cropBounded)
.

Definition crop_left {T : Type} {n : nat} (f : Idx (S n) -> T) : Idx n -> T :=
  fun i => f (idx (S n) (S(to_nat i)) cropleftBounded)
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
  
Definition expandBounded {n : nat} {n' : nat} (H : S n < S (S n')) :
  n < (S n').
Proof.
  apply le_S_n. apply H.
Qed.

Definition expand_left {T : Type} {n : nat} : (Idx n -> T) -> T -> Idx (S n) -> T :=
  match n with
  | 0 => fun f im i => im
  | S n' => fun f im i =>
            match i with
            | idx _ 0 H => im
            | idx _ (S n'') H => f (idx _ n'' (expandBounded H))
            end
end.

Definition reverse {T : Type} {n : nat} : (Idx n -> T) -> Idx n -> T :=
  fun f i => f (idx n (n - 1 - to_nat i) reverseBounded).

Definition expand {T : Type} {n : nat} (f :Idx n -> T) (im : T) : Idx (S n) -> T :=
  (reverse (expand_left (reverse f) im)).

Fixpoint rtake_left {T : Type} {n : nat} (b : nat) (err : T) : (Idx n -> T) -> (Idx b -> T) :=
  match n,b with
  | _,0 => fun f i => err
  | 0, S b => fun f i => err
  | S n', S b' => fun (f : Idx (S n') -> T) => expand (rtake_left b' err (crop_left f)) (f zero)
end.

Fixpoint rtake_right {T : Type} {n : nat} (a : nat) (err : T) : (Idx n -> T) -> (Idx (n-a) -> T) :=
  match n,a with
  | 0,_ => fun f i => err
  | S n',0 => fun (f : Idx (S n') -> T) => (f : Idx ((S n') - 0) -> T)
  | S n', S a' => fun (f : Idx (S n') -> T) => rtake_right a' err (crop f)
end.

Definition take_left  {T : Type} {n : nat} (b : nat) (err : T) (f : (Idx n -> T)) : (Idx b -> T) :=
  reverse (rtake_left b err f)
.

Definition take_right  {T : Type} {n : nat} (a : nat) (err : T) (f : (Idx n -> T)) : (Idx (n-a) -> T) :=
  reverse (rtake_right a err (reverse f))
.

Definition shift {T : Type} {n : nat} {a : nat} {b : nat} (err : T) : (Idx n -> T) -> (Idx (b-a) -> T) :=
  fun f => take_right a err (take_left b err f)
.


