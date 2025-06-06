
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
Require Import PeanoNat.

Inductive List (T : Type) : Type :=
  | Nil : List T
  | Cons (h : T) (tl : List T) : List T
.

Axiom FunEquality :
  forall (T1 : Type) (T2 : Type) (f : T1 -> T2) (g : T1 -> T2),
  f = g <-> forall (x : T1), f x = g x
.

Notation "h :: tl" := (Cons _ h tl).

Fixpoint ViewArray (d : List nat) : Type :=
  match d with
  | Nil _ => nat
  | n :: tl => Idx n -> (ViewArray tl)
end.

Notation "[[ T ; n ]]" := (ViewArray (n::T)).
Notation "[[; n ]]" := (ViewArray (n::(Nil nat))).
Notation "[[ [[ T ; m ]] ; n ]]" := (ViewArray (n::m::T)).

Definition to_view (n : nat) : [[; n]] :=
  fun i => to_nat i.


Definition reverse {T : List nat} {l : nat} (v : [[T;l]]) : [[T;l]] :=
  fun i => v (to_Idx l (l - 1 - (to_nat i)) reverseProof)
.

Definition select  {T :List nat} {l : nat} (a : nat) (b : nat) (v : [[T;b+l]]) : [[T;b - a]] :=
  fun i => v (to_Idx (b+l) (a + to_nat i) selectProof)
.

Definition group {T : List nat} (m : nat) (n : nat) (v : [[T ; m*n]]) : [[ [[T;m]] ; n]] :=
  fun j i => v (to_Idx (m*n) (to_nat j + n*(to_nat i)) groupProof)
.

Definition transpose {T : List nat} {m : nat} {n : nat} (v : [[ [[T;m]] ; n]]) : [[ [[T;n]] ; m]] :=
  fun i j => v j i
.

Definition map {A : List nat} {B : List nat} {n : nat} (f : ViewArray A -> ViewArray B) (v : [[A;n]]) : [[B;n]] :=
  fun i => f (v i)
.

(* Forces every total evaluation of a multi-dimensional array to have different images *)
Fixpoint saturateEquality {T : List nat} : ViewArray T -> ViewArray T -> List nat -> List nat -> Prop :=
  match T with
  | Nil _ => fun (x : ViewArray (Nil _)) (y : ViewArray (Nil _)) (lx : List nat) (ly : List nat) => x = y -> lx = ly
  | n::tl => fun (t : [[tl;n]]) (t' : [[tl;n]]) (lx : List nat) (ly : List nat) => forall (x : Idx n) (y : Idx n),
    saturateEquality (t x) (t' y) ((to_nat x)::lx) ((to_nat y)::ly)
end.

(* TODO : replace this definition using saturateEquality *)
Definition isInjective {T : List nat} {n : nat} (t : [[T;n]]) : Prop :=
  forall (i : Idx n) (j : Idx n), t i = t j -> i = j.

Proposition to_view_is_injective :
  forall (n : nat), isInjective (to_view n).
Proof.
  unfold isInjective. unfold saturateEquality. unfold to_view. intros. apply to_nat_injective in H. apply H.
Qed.

Proposition reverse_conserve_view :
  forall (T:List nat) (n : nat) (t : [[T;n]]), isInjective t -> isInjective (reverse t).
Proof.
    unfold isInjective. unfold saturateEquality. intros. unfold reverse in H0. apply H in H0.
    inversion H0. apply sub_injective with (c := n - 1) in H2. apply to_nat_injective in H2. apply H2.
    + destruct n. assert (to_nat i < 0). apply BoundedInt. inversion H1. simpl. rewrite Nat.sub_0_r.
    assert (S (to_nat i) <= S n). apply BoundedInt. apply le_S_n in H1. apply H1. 
    + destruct n. assert (to_nat j < 0). apply BoundedInt. inversion H1. simpl. rewrite Nat.sub_0_r.
    assert (S (to_nat j) <= S n). apply BoundedInt. apply le_S_n in H1. apply H1. 
Qed.

Proposition select_conserve_view :
  forall T a b k (t : [[T;b+k]]), isInjective t -> isInjective (select a b t).
Proof.
  unfold isInjective. unfold saturateEquality.
  unfold select.
  intros.
  apply H in H0. inversion H0. apply add_injective in H2. apply to_nat_injective in H2. apply H2.
Qed.

Definition isInjective2 {T : List nat} {n : nat} {m : nat} (t : [[[[T;m]];n]]) : Prop :=
  forall (i1 : Idx n) (j1 : Idx m) (i2 : Idx n) (j2 : Idx m), t i1 j1 = t i2 j2 -> (i1,j1) = (i2,j2).

Proposition group_conserve_view :
  forall T m n (t : [[T;m*n]]), isInjective t -> isInjective2 (group m n t).
Proof.
  unfold isInjective. unfold isInjective2. unfold group.
  intros.
  apply H in H0.
  inversion H0.
  assert ((to_nat i1,to_nat j1) = (to_nat i2,to_nat j2)).
  apply projection_injective with (k := n). apply BoundedInt. apply BoundedInt. apply H2.
  injection H1. intros. apply to_nat_injective in H3. rewrite H3.  apply to_nat_injective in H4. rewrite H4. reflexivity.
Qed.

Proposition transpose_conserve_view :
  forall T m n (t : [[[[T;m]];n]]), isInjective2 t -> isInjective2 (transpose t).
Proof.
  unfold isInjective2. unfold transpose.
  intros.
  apply H in H0. injection H0. intros. subst. reflexivity.
Qed.