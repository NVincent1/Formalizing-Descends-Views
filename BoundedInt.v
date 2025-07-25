Require Import PeanoNat.


Inductive Idx (s : nat) : Type := 
  | idx (n : nat) (H : n < s) : Idx s.

Definition to_nat {s : nat} (i : Idx s) : nat :=
  match i with
  | idx _ n _ => n
end.

Definition to_Idx (s : nat) (n : nat) (H : s > n) : Idx s :=
  idx _ n H
.

Theorem BoundedInt :
  forall (n : nat) (i : Idx n),
  (to_nat i) < n.
Proof.
  intros.
  destruct i. apply H.
Qed.

Definition zero {n : nat} :=
  idx (S n) 0 (Nat.lt_0_succ n).

Definition maxIdx {n : nat} :=
  idx (S n) n (le_n (S n)).

(* Equality between two bounded integers of the same value, but with different proofs (reflexivity fails) *)
Axiom unif_Idx :
  forall (n : nat) (s : nat) (H1 : n < s) (H2 : n < s), idx s n H1 = idx s n H2.

Theorem to_nat_injective :
  forall s (i : Idx s) (j : Idx s), to_nat i = to_nat j -> i = j.
Proof.
  intros. destruct i; destruct j.
    simpl in H. subst. apply unif_Idx.
Qed.


(** Proofs needed for the definition of the functions in `Views.v` *)

Definition reverseBounded {l : nat} {i : Idx l} :
  l > l - 1 - to_nat i.
Proof.
  destruct i as [i Hi].
  destruct l. inversion Hi. simpl. unfold gt. unfold lt. rewrite Nat.sub_0_r. apply le_n_S. apply Nat.le_sub_l.
Qed.

Definition takeleftBounded {b : nat} {n : nat} {i : Idx b} :
 to_nat i < b + n.
Proof.
  apply Nat.lt_lt_add_r.
  apply BoundedInt.
Qed.

Definition takerightBounded {a : nat} {n : nat} {i : Idx n} :
 a + to_nat i < a + n.
Proof.
  apply Nat.add_lt_mono_l.
  apply BoundedInt.
Qed.

Definition selectrangeBounded {a : nat} {b : nat} {n : nat} {i : Idx (b-a)} :
  a + to_nat i < b + n.
Proof.
  destruct i.
  simpl.
  destruct (b-a) eqn:E.
  - inversion H.
  - assert (S n1 <> 0). intro. inversion H0.
    apply Nat.add_sub_eq_nz with (m := a) (n := b) in H0.
    assert (a + n0 < a + S n1). apply Nat.add_lt_mono_l. apply H.
    rewrite H0 in H1. apply Nat.le_trans with (m := b). apply H1. apply Nat.le_add_r. apply E.
Qed.

Definition groupBounded {m : nat} {n : nat} {i : Idx m} {j : Idx n} :
  m * n > to_nat i + m * to_nat j.
Proof.
  destruct i as [ni Hi]; destruct j as [nj Hj].
  simpl.
  destruct n.
  - inversion Hj.
  - rewrite Nat.mul_succ_r. rewrite Nat.add_comm. unfold gt. unfold lt. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono.
  apply Hi. subst. apply Nat.mul_le_mono_l. apply le_S_n in Hj. apply Hj.
Qed.