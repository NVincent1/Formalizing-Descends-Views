Require Import PeanoNat.
From Views Require Import Lemmas.


Inductive Idx (s : nat) : Type := 
  | Id (n : nat) (H : n < s) : Idx s.

Definition to_nat {s : nat} (i : Idx s) : nat :=
  match i with
  | Id _ n _ => n
end.

Definition to_Idx (s : nat) (n : nat) (H : s > n) : Idx s :=
  Id _ n H
.

Theorem BoundedInt :
  forall (n : nat) (i : Idx n),
  (to_nat i) < n.
Proof.
  intros.
  unfold to_nat. destruct i. apply H.
Qed.

Axiom unif_Idx :
  forall (n : nat) (s : nat) (H1 : n < s) (H2 : n < s), Id _ n H1 = Id _ n H2.

Theorem to_nat_injective :
  forall s (i : Idx s) (j : Idx s), to_nat i = to_nat j -> i = j.
Proof.
  intros. destruct i; destruct j.
    simpl in H. subst. apply unif_Idx.
Qed.



Definition reverseProof {l : nat} {i : Idx l} :
  l > l - 1 - to_nat i.
Proof.
  destruct i as [i Hi].
  destruct l. inversion Hi. simpl. unfold gt. unfold lt. rewrite Nat.sub_0_r. apply le_n_S. apply Nat.le_sub_l.
Qed.

Definition takeleftProof {b : nat} {n : nat} {i : Idx b} :
 to_nat i < b + n.
Proof.
  apply Nat.lt_lt_add_r.
  apply BoundedInt.
Qed.

Definition takerightProof {a : nat} {n : nat} {i : Idx (n-a)} :
 a + to_nat i < a + n.
Proof.
  apply Nat.add_lt_mono_l.
  destruct i.
  simpl.
  assert (n - a <= n). apply Nat.le_sub_l.
  apply Nat.le_trans with (m := (n-a)).
  apply H. apply H0.
Qed.

Definition groupProof {m : nat} {n : nat} {i : Idx m} {j : Idx n} :
  m * n > to_nat i + m * to_nat j.
Proof.
  destruct i as [ni Hi]; destruct j as [nj Hj].
  simpl.
  destruct n.
  - inversion Hj.
  - rewrite Nat.mul_succ_r. rewrite Nat.add_comm. unfold gt. unfold lt. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono.
  apply Hi. subst. apply Nat.mul_le_mono_l. apply le_S_n in Hj. apply Hj.
Qed.

Definition modProof {n : nat} {i : Idx n} (H : n <> 0):
  n > to_nat i mod n.
Proof.
  apply Nat.mod_upper_bound with (a := to_nat i) in H. apply H.
Qed.
