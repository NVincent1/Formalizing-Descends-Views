
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