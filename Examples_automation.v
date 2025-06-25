
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
From Ltac2 Require Import Ltac2.
From Views Require Import Tactic.
Require Import PeanoNat.

(** Proofs that are in `ViewsProof.v` using the automated tactics from `Tactic.v`.
Does not contain the proof of `map` preserving injectivity as it is not easily automatable by
following a similar pattern as the others *)

Theorem reverse_preserves_injectivity_auto_proof : forall T n, preserve_Injectivity reverse (A := (n::T)).
Proof.
  intros T n.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx n (n - 1 - to_nat i) reverseProof,tx) end).
  assert (H':forall (x y : Idx n), n - 1 - to_nat x = n - 1 - to_nat y -> x = y). {
    (* assertion : the reordering function used by reverse is injective *)
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

Theorem take_left_preserves_injectivity_auto_proof : forall T n b, preserve_Injectivity (take_left b) (A := ((b+n)::T)).
Proof.
  intros T n b.
  set (function := fun (x : Tuple (b::T)) => match x with | (i,tx) => (idx (b+n) (to_nat i) takeleftProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply to_nat_injective in H0. subst. reflexivity.
  - apply to_nat_injective in H2. subst. reflexivity.
Qed.

Theorem select_range_preserves_injectivity_auto_proof : forall T n a b, preserve_Injectivity (select_range a b) (A := ((b+n)::T)).
Proof.
  intros T n a b.
  set (function := fun (x : Tuple ((b-a)::T)) => match x with | (i,tx) => (idx (b+n) (a + to_nat i) selectrangeProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply add_injective in H0. apply to_nat_injective in H0. subst. reflexivity.
  - apply add_injective in H2. apply to_nat_injective in H2. subst. reflexivity.
Qed.

Theorem take_right_preserves_injectivity_auto_proof : forall T n a, preserve_Injectivity (take_right a) (A := ((a+n)::T)).
Proof.
  intros T n a.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx (a+n) (a + to_nat i) takerightProof,tx) end).
  reordering_autoProof ('function) (@function) 0.
  - apply add_injective in H0. apply to_nat_injective in H0. subst. reflexivity.
  - apply add_injective in H2. apply to_nat_injective in H2. subst. reflexivity.
Qed.

Theorem transpose_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity transpose (A := (m::n::T)).
Proof.
  intros T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (j,(i,tx)) end).
  reordering_autoProof ('function) (@function) 1;
  reflexivity.
Qed.

Theorem group_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity (group m) (A := (m*n::T)).
Proof.
  intros T n m.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (idx (m*n) (to_nat j + m*(to_nat i)) groupProof,tx) end).
  assert (H':forall (x1 y1 : Idx m) (x2 y2 : Idx n), to_nat x1 + m * to_nat x2 = to_nat y1 + m * to_nat y2 -> (x1,x2) = (y1,y2)). {
    (* assertion : the reordering function used by reverse is injective *)
    intros.
    apply projection_injective in H. inversion H. apply to_nat_injective in H1. apply to_nat_injective in H2. subst. reflexivity.
    apply BoundedInt. apply BoundedInt.
  }
  reordering_autoProof ('function) (@function) 1.
  apply H' in H0; inversion H0; subst; reflexivity.
  apply H' in H2; inversion H2; subst; reflexivity.
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

Definition swap {T : List nat} {n : nat} (i : Idx n) (j : Idx n) (v : ViewArray [[T;n]]) : ViewArray [[T;n]] :=
  fun i' => if (eqb (to_nat i') (to_nat i)) then v j else if (eqb (to_nat i') (to_nat j)) then v i else v i'.

Theorem test_auto_swap :
  forall T n (i j : Idx n), preserve_Injectivity (swap i j) (A := (n::T)).
Proof.
  intros T n i j.
  set (function := fun (x : Tuple (n::T)) => match x with | (i',tx) => (if (eqb (to_nat i') (to_nat i)) then j else if (eqb (to_nat i') (to_nat j)) then i else i',tx) end).
  auto_destruct 0;
  (* destruct equalities *)
  destruct (eqb (to_nat i0) (to_nat i)) eqn:Ex;
  destruct (eqb (to_nat i0) (to_nat j)) eqn:Ex';
  destruct (eqb (to_nat i1) (to_nat i)) eqn:Ey;
  destruct (eqb (to_nat i1) (to_nat j)) eqn:Ey';
  unfold swap in *; simpl in Hypothesis1;
  (* replace eqb by actual equalities *)
  try (rewrite Ex in Hypothesis1);
  try (apply eqb_impl_eq in Ex; apply to_nat_injective in Ex);
  try (rewrite Ex' in Hypothesis1);
  try (apply eqb_impl_eq in Ex'; apply to_nat_injective in Ex');
  try (rewrite Ey in Hypothesis1);
  try (apply eqb_impl_eq in Ey; apply to_nat_injective in Ey);
  try (rewrite Ey' in Hypothesis1);
  try (apply eqb_impl_eq in Ey'; apply to_nat_injective in Ey');
  auto_apply(); try reflexivity. (* solve 24 of the 32 cases *)
  (* manually handling the absurd cases *)
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
  forall T n (f : Idx n -> Idx n), (forall x y, f x = f y -> x = y) -> preserve_Injectivity (fun v i => v (f i)) (A := n::T)  (B := (n::T)).
Proof.
  intros T n f Hf.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,ti) => (f i,ti) end).
  reordering_autoProof ('function) (@function) 0.
  apply Hf in H0. subst. reflexivity.
  apply Hf in H2. subst. reflexivity.
Qed.

