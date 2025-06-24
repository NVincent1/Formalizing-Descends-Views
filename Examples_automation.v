
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
  reordering_autoProof ('function) (@function) 1;
  reflexivity.
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
  reordering_autoProof1 1;
  unfold group in *; simpl in Hypothesis1;
  applyHinj_all().
  apply H' in H1; inversion H1; subst; reflexivity.
  apply H' in H3; inversion H3; subst; reflexivity.
Qed.

Fixpoint eqb (m : nat) (n : nat) :=
  match (m,n) with
  | (0,0) => true
  | (S m, S n) => eqb m n
  | (_,_) => false
end.

Lemma eqb_impl_eq :
  forall m n,
  eqb m n = true -> m = n.
Proof.
  induction m.
  - destruct n. intro. reflexivity. intro. inversion H.
  - destruct n. intro. inversion H. simpl. intro. apply IHm in H. rewrite H. reflexivity.
Qed.

Lemma eqb_n_n :
  forall n,
  eqb n n = true.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Definition swap {l : nat} {T : List nat} {n : nat} (i : Idx n) (j : Idx n) (v : ViewArray l [[T;n]]) : ViewArray l [[T;n]] :=
  fun i' => if (eqb (to_nat i') (to_nat i)) then v j else if (eqb (to_nat i') (to_nat j)) then v i else v i'.

Theorem test_auto_swap :
  forall l T n (i j : Idx n), preserve_Injectivity (swap i j) (l := l) (A := (n::T)).
Proof.
  intros l T n i j.
  set (function := fun (x : Tuple (n::T)) => match x with | (i',tx) => (if (eqb (to_nat i') (to_nat i)) then j else if (eqb (to_nat i') (to_nat j)) then i else i',tx) end).
  reordering_autoProof1 0;
  destruct (eqb (to_nat i0) (to_nat i)) eqn:Ex;
  destruct (eqb (to_nat i0) (to_nat j)) eqn:Ex';
  destruct (eqb (to_nat i1) (to_nat i)) eqn:Ey;
  destruct (eqb (to_nat i1) (to_nat j)) eqn:Ey';
  unfold swap in *; simpl in Hypothesis1;
  try (rewrite Ex in Hypothesis1);
  try (apply eqb_impl_eq in Ex; apply to_nat_injective in Ex);
  try (rewrite Ex' in Hypothesis1);
  try (apply eqb_impl_eq in Ex'; apply to_nat_injective in Ex');
  try (rewrite Ey in Hypothesis1);
  try (apply eqb_impl_eq in Ey; apply to_nat_injective in Ey);
  try (rewrite Ey' in Hypothesis1);
  try (apply eqb_impl_eq in Ey'; apply to_nat_injective in Ey');
  applyHinj_all(); try reflexivity. (* solve 24 of the 32 cases *)
  rewrite eqb_n_n in Ey';inversion Ey'.
  rewrite eqb_n_n in Ey;inversion Ey.
  rewrite eqb_n_n in Ex';inversion Ex'.
  rewrite eqb_n_n in Ex;inversion Ex.
  rewrite eqb_n_n in Ey';inversion Ey'.
  rewrite eqb_n_n in Ey;inversion Ey.
  rewrite eqb_n_n in Ex';inversion Ex'.
  rewrite eqb_n_n in Ex;inversion Ex.
Qed.

Theorem test_auto_permutation :
  forall l T n (f : Idx n -> Idx n), (forall x y, f x = f y -> x = y) -> preserve_Injectivity (fun v i => v (f i)) (l := l) (A := n::T)  (B := (n::T)).
Proof.
  intros l T n f Hf.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,ti) => (f i,ti) end).
  reordering_autoProof ('function) (@function) 0.
  apply Hf in H0. subst. reflexivity.
  apply Hf in H2. subst. reflexivity.
Qed.

