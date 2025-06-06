Require Import PeanoNat.
From Views Require Import Lemmas.


Inductive Idx (s : nat) : Type := 
  | I (n : nat) (H : n < s) : Idx s.

Definition to_nat {s : nat} (i : Idx s) : nat :=
  match i with
  | I _ n _ => n
end.

Definition to_Idx (s : nat) (n : nat) (H : s > n) : Idx s :=
  I _ n H
.

Theorem BoundedInt :
  forall (n : nat) (i : Idx n),
  (to_nat i) < n.
Proof.
  intros.
  unfold to_nat. destruct i. apply H.
Qed.

Axiom unif_Idx :
  forall (n : nat) (s : nat) (H1 : n < s) (H2 : n < s), I _ n H1 = I _ n H2.

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

Definition selectProof {b : nat} {a : nat} {l : nat} {i : Idx (b-a)}:
  b + l > a + to_nat i.
Proof.
  destruct i as [n Hi]. simpl.
  assert (a + n < b). {
    destruct (b-a) eqn:E.
    - inversion Hi.
    - unfold lt in Hi. apply Nat.add_le_mono_r with (p := a) in Hi. simpl in Hi. rewrite Nat.add_comm in Hi.
    assert (b - a + a = b). {
        apply Nat.sub_add. Search "-". apply Nat.add_sub_eq_nz in E. rewrite <- E. Search "+". apply Nat.le_add_r. intro. inversion H.
    } assert (S (n0 + a) = b - a + a).  rewrite <- Nat.add_succ_l. rewrite <- E. reflexivity. rewrite H0 in Hi.
    rewrite <- H. apply Hi.
    }
    apply Nat.le_trans with (m := b). apply H. apply Nat.le_add_r. 
Qed.

Definition groupProof {m : nat} {n : nat} {i : Idx m} {j : Idx n} :
  m * n > to_nat j + n * to_nat i.
Proof.
  destruct i as [ni Hi]; destruct j as [nj Hj].
  simpl.
  rewrite Nat.mul_comm.
  destruct m.
  - inversion Hi.
  - rewrite Nat.mul_succ_r. rewrite Nat.add_comm. unfold gt. unfold lt. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono.
  apply Hj. subst. apply Nat.mul_le_mono_l. apply le_S_n in Hi. apply Hi.
Qed.
