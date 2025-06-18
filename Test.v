
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
From Ltac2 Require Import Ltac2.
From Views Require Import Tactic.
Require Import PeanoNat.


Theorem testreverse : forall T n, curry_Injective reverse (A := (n::T)).
Proof.
  intros T n.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx n (n - 1 - to_nat i) reverseProof,tx) end).
  autoProof ('function) (@function) 0.
  - apply sub_injective in H1.
    apply to_nat_injective in H1. subst. reflexivity.
    destruct n. destruct i0 as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct i1 as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  - apply sub_injective in H3.
    apply to_nat_injective in H3. subst. reflexivity.
    destruct n. destruct i0 as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct i1 as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
Qed.

Theorem testtakeleft : forall T n b, curry_Injective (take_left b) (A := ((b+n)::T)).
Proof.
  intros T n b.
  set (function := fun (x : Tuple (b::T)) => match x with | (i,tx) => (idx (b+n) (to_nat i) takeleftProof,tx) end).
  autoProof ('function) (@function) 0.
  - apply to_nat_injective in H1. subst. reflexivity.
  - apply to_nat_injective in H3. subst. reflexivity.
Qed.

Theorem testtakeright : forall T n a, curry_Injective (take_right a) (A := ((a+n)::T)).
Proof.
  intros T n a.
  set (function := fun (x : Tuple ((n-a)::T)) => match x with | (i,tx) => (idx (a+n) (a + to_nat i) takerightProof,tx) end).
  autoProof ('function) (@function) 0.
  - apply add_injective in H1. apply to_nat_injective in H1. subst. reflexivity.
  - apply add_injective in H3. apply to_nat_injective in H3. subst. reflexivity.
Qed.

Theorem testtranspose : forall T n m, curry_Injective transpose (A := (m::n::T)).
Proof.
  intros T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (j,(i,tx)) end).
  autoProof ('function) (@function) 1.
  - reflexivity.
  - reflexivity.
Qed.

Theorem testgroup : forall T n m, curry_Injective (group m) (A := (m*n::T)).
Proof.
  intros T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (idx (m*n) (to_nat j + m*(to_nat i)) groupProof,tx) end).
  autoProof ('function) (@function) 1.
  - apply projection_injective in H1. inversion H1. apply to_nat_injective in H2. apply to_nat_injective in H3. subst. reflexivity.
  apply BoundedInt. apply BoundedInt.
  - apply projection_injective in H3. inversion H3. apply to_nat_injective in H1. apply to_nat_injective in H2. subst. reflexivity.
  apply BoundedInt. apply BoundedInt.
Qed.