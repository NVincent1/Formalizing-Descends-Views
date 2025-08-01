
From Views Require Import Injectivity_Lemmas.
From Views Require Import BoundedInt.
From Views Require Import utils.
From Views Require Import Views.
From Views Require Import Proof.
From Ltac2 Require Import Ltac2.
From Views Require Import Tactic.
Require Import PeanoNat.

(** Proofs that are in `ViewsProof.v` using the automated tactics from `Tactic.v`.
Does not contain the proof of `map` preserving injectivity as it is not easily automatable by
following a similar pattern as the others *)

Proposition reverse_preserves_injectivity_auto_proof : forall T n, preserve_Injectivity (view reverse) (A := (n::T)).
Proof.
  intros T n.
  assert (H':forall (x y : Idx n), n - 1 - to_nat x = n - 1 - to_nat y -> x = y). {
    (* assertion : the reordering function used by reverse is injective *)
    intros.
    apply sub_injective in H.
    apply to_nat_injective in H. subst. reflexivity.
    destruct n. destruct x as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  }
  reordering_autoProof 1.
  apply H' in H1; subst; reflexivity.
Qed.

Proposition take_left_preserves_injectivity_auto_proof : forall T n b, preserve_Injectivity (view (take_left b)) (A := ((b+n)::T)).
Proof.
  intros T n b.
  reordering_autoProof 1.
  apply to_nat_injective in H1. subst. reflexivity.
Qed.

Proposition take_right_preserves_injectivity_auto_proof : forall T n a, preserve_Injectivity (view (take_right a)) (A := ((a+n)::T)).
Proof.
  intros T n a.
  reordering_autoProof 1.
  apply add_injective in H1. apply to_nat_injective in H1. subst. reflexivity.
Qed.

Proposition select_range_preserves_injectivity_auto_proof : forall T n a b, preserve_Injectivity (view (select_range a b)) (A := ((b+n)::T)).
Proof.
  intros T n a b.
  reordering_autoProof 1.
  apply add_injective in H1. apply to_nat_injective in H1. subst. reflexivity.
Qed.

Proposition transpose_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity (view transpose) (A := (m::n::T)).
Proof.
  intros T n m.
  reordering_autoProof 2.
  reflexivity.
Qed.

Proposition group_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity (view (group m)) (A := (m*n::T)).
Proof.
  intros T n m.
  assert (H':forall (x1 y1 : Idx m) (x2 y2 : Idx n), to_nat x1 + m * to_nat x2 = to_nat y1 + m * to_nat y2 -> (x1,x2) = (y1,y2)). {
    (* assertion : the reordering function used by reverse is injective *)
    intros.
    apply projection_injective in H. inversion H. apply to_nat_injective in H1. apply to_nat_injective in H2. subst. reflexivity.
    apply BoundedInt. apply BoundedInt.
  }
  reordering_autoProof 2.
  apply H' in H1; inversion H1; subst; reflexivity.
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
  fun x => match x with (i',x) => (if (eqb (to_nat i') (to_nat i)) then j else if (eqb (to_nat i') (to_nat j)) then i else i',x) end.

Proposition test_auto_swap :
  forall T n (i j : Idx n), preserve_Injectivity (view (swap i j)) (A := (n::T)).
Proof.
  intros T n i j.
  reordering_autoProof 1.
  (* destruct equalities *)
  destruct (eqb (to_nat i0) (to_nat i)) eqn:Ex;
  destruct (eqb (to_nat i0) (to_nat j)) eqn:Ex';
  destruct (eqb (to_nat i1) (to_nat i)) eqn:Ey;
  destruct (eqb (to_nat i1) (to_nat j)) eqn:Ey';
  unfold swap in *; simpl in H;
  (* replace eqb by actual equalities *)
  try (rewrite Ex in H);
  try (apply eqb_impl_eq in Ex; apply to_nat_injective in Ex);
  try (rewrite Ex' in H);
  try (apply eqb_impl_eq in Ex'; apply to_nat_injective in Ex');
  try (rewrite Ey in H);
  try (apply eqb_impl_eq in Ey; apply to_nat_injective in Ey);
  try (rewrite Ey' in H);
  try (apply eqb_impl_eq in Ey'; apply to_nat_injective in Ey');
  subst; try reflexivity. (* solve 12 of the 16 cases *)
  (* manually handling the absurd cases *)
  rewrite eqb_n_n in Ey';inversion Ey'.
  rewrite eqb_n_n in Ey;inversion Ey.
  rewrite eqb_n_n in Ex';inversion Ex'.
  rewrite eqb_n_n in Ex;inversion Ex.
Qed.

Proposition flatten_preserves_injectivity_auto_proof : forall T n m, preserve_Injectivity (view (flatten m)) (A := (n::m::T)).
Proof.
  intros T n m.
  reordering_autoProof 1.
  assert (H': i = i0). {
    apply to_nat_injective.
    rewrite Nat.Div0.div_mod with (a := to_nat i) (b := m).
    rewrite Nat.Div0.div_mod with (a := to_nat i0) (b := m).
    rewrite H1. rewrite H2. reflexivity.
  }
  rewrite H'; reflexivity.
Qed.

