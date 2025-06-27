
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
(* From Ltac2 Require Import Ltac2.
From Views Require Import Tactic. *)
Require Import PeanoNat.

(** Proofs that are in `ViewsProof.v` using the automated tactics from `Tactic.v`.
Does not contain the proof of `map` preserving injectivity as it is not easily automatable by
following a similar pattern as the others *)

Theorem reverse_preserves_injectivity_auto_proof : forall T n, preserve_Injectivity (view reverse) (A := (n::T)).
Proof.
  intros T n.
  apply injective_functions_preserve_injectivity.
  intros. destruct x as [x tx], y as [y ty].
  inversion H.
  apply sub_injective in H1.
  apply to_nat_injective in H1. subst. reflexivity.
  destruct n. destruct x as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  destruct n. destruct y as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
Qed.

Theorem take_left_preserves_injectivity_auto_proof : forall T n b, preserve_Injectivity (view (take_left b)) (A := ((b+n)::T)).
Proof.
  intros T n b.
  apply injective_functions_preserve_injectivity.
  intros. destruct x as [x tx], y as [y ty].
  inversion H.
  apply to_nat_injective in H1.
  subst; reflexivity.
Qed.

Theorem take_right_preserves_injectivity_auto_proof : forall T n a, preserve_Injectivity (view (take_right a)) (A := ((a+n)::T)).
Proof.
  intros T n a.
  apply injective_functions_preserve_injectivity.
  intros. destruct x as [x tx], y as [y ty].
  inversion H.
  apply add_injective in H1. apply to_nat_injective in H1.
  subst; reflexivity.
Qed.

Theorem select_range_preserves_injectivity_auto_proof : forall T n a b, preserve_Injectivity (view (select_range a b)) (A := ((b+n)::T)).
Proof.
  intros T n a b.
  apply injective_functions_preserve_injectivity.
  intros. destruct x as [x tx], y as [y ty].
  inversion H.
  apply add_injective in H1. apply to_nat_injective in H1.
  subst; reflexivity.
Qed.

Theorem transpose_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity (view transpose) (A := (m::n::T)).
Proof.
  intros T n a b.
  apply injective_functions_preserve_injectivity.
  unfold transpose.
  intros. destruct x as [xi tx], tx as [xj tx], y as [yi ty], ty as [yj ty].
  inversion H;subst;reflexivity.
Qed.

Theorem group_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity (view (group m)) (A := (m*n::T)).
Proof.
  intros T n m.
  apply injective_functions_preserve_injectivity.
  intros. destruct x as [xi tx], tx as [xj tx], y as [yi ty], ty as [yj ty].
  inversion H.
  apply projection_injective in H1.
  inversion H1.
  apply to_nat_injective in H3.
  apply to_nat_injective in H4.
  subst;reflexivity.
  apply BoundedInt. apply BoundedInt.
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

Definition swap {T : List nat} {n : nat} (i : Idx n) (j : Idx n) : Tuple (n::T) -> Tuple (n::T) :=
  fun x => match x with | (i',x) => (if (eqb (to_nat i') (to_nat i)) then j else if (eqb (to_nat i') (to_nat j)) then i else i',x) end.

Theorem test_auto_swap :
  forall T n (i j : Idx n), preserve_Injectivity (view (swap i j)) (A := (n::T)).
Proof.
  intros T n i j.
  apply injective_functions_preserve_injectivity.
  unfold swap.
  intros.
  destruct x as [i0 tx],y as [i1 ty].
  (* destruct equalities *)
  destruct (eqb (to_nat i0) (to_nat i)) eqn:Ex;
  destruct (eqb (to_nat i0) (to_nat j)) eqn:Ex';
  destruct (eqb (to_nat i1) (to_nat i)) eqn:Ey;
  destruct (eqb (to_nat i1) (to_nat j)) eqn:Ey';
  (* replace eqb by actual equalities *)
  try (rewrite Ex in Hypothesis1);
  try (apply eqb_impl_eq in Ex; apply to_nat_injective in Ex);
  try (rewrite Ex' in Hypothesis1);
  try (apply eqb_impl_eq in Ex'; apply to_nat_injective in Ex');
  try (rewrite Ey in Hypothesis1);
  try (apply eqb_impl_eq in Ey; apply to_nat_injective in Ey);
  try (rewrite Ey' in Hypothesis1);
  try (apply eqb_impl_eq in Ey'; apply to_nat_injective in Ey');
  inversion H; subst; try reflexivity.
  (* handling the absurd cases *)
  rewrite eqb_n_n in Ey';inversion Ey'.
  rewrite eqb_n_n in Ey;inversion Ey.
  rewrite eqb_n_n in Ex';inversion Ex'.
  rewrite eqb_n_n in Ex;inversion Ex.
Qed.

