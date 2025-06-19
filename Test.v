
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
From Ltac2 Require Import Ltac2.
From Views Require Import Tactic.
Require Import PeanoNat.


Theorem test_auto_reverse : forall T n, preserve_Injectivity reverse (A := (n::T)).
Proof.
  intros T n.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx n (n - 1 - to_nat i) reverseProof,tx) end).
  assert (H':forall (x y : Idx n), n - 1 - to_nat x = n - 1 - to_nat y -> x = y). {
    intros.
    apply sub_injective in H.
    apply to_nat_injective in H. subst. reflexivity.
    destruct n. destruct x as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  }
  reordering_autoProof ('function) (@function) 0.
  apply H' in H1; subst; reflexivity.
  apply H' in H3; subst; reflexivity.
Qed.

Theorem test_auto_take_left : forall T n b, preserve_Injectivity (take_left b) (A := ((b+n)::T)).
Proof.
  intros T n b.
  set (function := fun (x : Tuple (b::T)) => match x with | (i,tx) => (idx (b+n) (to_nat i) takeleftProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply to_nat_injective in H1. subst. reflexivity.
  - apply to_nat_injective in H3. subst. reflexivity.
Qed.

Theorem test_auto_take_right : forall T n a, preserve_Injectivity (take_right a) (A := ((a+n)::T)).
Proof.
  intros T n a.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx (a+n) (a + to_nat i) takerightProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply add_injective in H1. apply to_nat_injective in H1. subst. reflexivity.
  - apply add_injective in H3. apply to_nat_injective in H3. subst. reflexivity.
Qed.

Theorem test_auto_transpose : forall T n m, preserve_Injectivity transpose (A := (m::n::T)).
Proof.
  intros T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (j,(i,tx)) end).
  reordering_autoProof ('function) (@function) 1; reflexivity.
Qed.

Theorem test_auto_group : forall T n m, preserve_Injectivity (group m) (A := (m*n::T)).
Proof.
  intros T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (idx (m*n) (to_nat j + m*(to_nat i)) groupProof,tx) end).
  assert (H':forall (x1 y1 : Idx m) (x2 y2 : Idx n), to_nat x1 + m * to_nat x2 = to_nat y1 + m * to_nat y2 -> (x1,x2) = (y1,y2)). {
    intros.
    apply projection_injective in H. inversion H. apply to_nat_injective in H1. apply to_nat_injective in H2. subst. reflexivity.
    apply BoundedInt. apply BoundedInt.
  }
  reordering_autoProof ('function) (@function) 1.
  apply H' in H1; inversion H1; subst; reflexivity.
  apply H' in H3; inversion H3; subst; reflexivity.
Qed.