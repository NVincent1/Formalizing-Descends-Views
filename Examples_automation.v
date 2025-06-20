
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
From Ltac2 Require Import Ltac2.
From Views Require Import Tactic.
Require Import PeanoNat.

Theorem test_auto_reverse : forall l T n, preserve_Injectivity reverse (l := l) (A := (n::T)).
Proof.
  intros l T n.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx n (n - 1 - to_nat i) reverseProof,tx) end).
  assert (H':forall (x y : Idx n), n - 1 - to_nat x = n - 1 - to_nat y -> x = y). {
    intros.
    apply sub_injective in H.
    apply to_nat_injective in H. subst. reflexivity.
    destruct n. destruct x as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  }
  reordering_autoProof ('function) (@function) 0.
  apply H' in H0; subst; reflexivity.
  apply H' in H2; subst; reflexivity.
Qed.

Theorem test_auto_take_left : forall l T n b, preserve_Injectivity (take_left b) (l := l) (A := ((b+n)::T)).
Proof.
  intros l T n b.
  set (function := fun (x : Tuple (b::T)) => match x with | (i,tx) => (idx (b+n) (to_nat i) takeleftProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply to_nat_injective in H0. subst. reflexivity.
  - apply to_nat_injective in H2. subst. reflexivity.
Qed.

Theorem test_auto_take_right : forall l T n a, preserve_Injectivity (take_right a) (l := l) (A := ((a+n)::T)).
Proof.
  intros l T n a.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx (a+n) (a + to_nat i) takerightProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply add_injective in H0. apply to_nat_injective in H0. subst. reflexivity.
  - apply add_injective in H2. apply to_nat_injective in H2. subst. reflexivity.
Qed.

Theorem test_auto_transpose : forall l T n m, preserve_Injectivity transpose (l := l) (A := (m::n::T)).
Proof.
  intros l T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (j,(i,tx)) end).
  reordering_autoProof ('function) (@function) 1; reflexivity.
Qed.

Theorem test_auto_group : forall l T n m, preserve_Injectivity (group m) (l := l) (A := (m*n::T)).
Proof.
  intros l T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (idx (m*n) (to_nat j + m*(to_nat i)) groupProof,tx) end).
  assert (H':forall (x1 y1 : Idx m) (x2 y2 : Idx n), to_nat x1 + m * to_nat x2 = to_nat y1 + m * to_nat y2 -> (x1,x2) = (y1,y2)). {
    intros.
    apply projection_injective in H. inversion H. apply to_nat_injective in H1. apply to_nat_injective in H2. subst. reflexivity.
    apply BoundedInt. apply BoundedInt.
  }
  reordering_autoProof ('function) (@function) 1.
  apply H' in H0; inversion H0; subst; reflexivity.
  apply H' in H2; inversion H2; subst; reflexivity.
Qed.



