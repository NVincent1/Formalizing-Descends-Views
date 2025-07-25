
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Proposition collection_correct :
  forall a n (v : Vector execution_resource n),
      exists (m : Vector nat n), (forall i, i < n -> count a (logical_thread_set (v i)) (m i)) ->
      count a (logical_thread_set (Collection n v)) (sum m)
.
Proof.
  induction n.
    - exists (fun i => i). intros. apply empty.
    - intros. assert (exists m : Vector nat n,
        (forall i : nat, i < n -> count a (logical_thread_set (v i)) (m i)) ->
        count a (logical_thread_set (Collection n v)) (sum m)). apply IHn.
      destruct H.
      assert (exists m, count a (logical_thread_set (v n)) m). apply count_exists.
      destruct H0.
      exists (fun i => if (eqb i n) then x0 else x i).
      intros.
      simpl. apply cat_count.
      * rewrite eqb_refl. apply H0.
      * assert (sum (n := n) (fun i : nat => if eqb i n then x0 else x i) = sum x).
        apply vector_sum_eq.
        intros. assert (eqb i n = false). apply eqb_correct_2.
        intro. subst. apply Nat.lt_irrefl in H2. apply H2. rewrite H3. reflexivity.
        rewrite H2. apply H.
        intros. assert (i < (S n)). apply le_S in H3. apply H3.
        apply H1 in H4. assert (eqb i n = false). apply eqb_correct_2.
        intro. subst. apply Nat.lt_irrefl in H3. apply H3. rewrite H5 in H4.
        apply H4.
Qed.

Proposition tensorcollection_correct :
  forall x y z (v : Tensor' execution_resource x y z),
      logical_thread_set (TensorCollection x y z v) =
      logical_thread_set (Collection x (fun i => Collection y (fun j => (Collection z (fun k => v i j k))))).
Proof.
  reflexivity.
Qed.

Fixpoint contains_tensorcollection (e : execution_resource) (P : execution_resource -> Prop) : Prop :=
  match e with
  | Collection n v => forall i, i < n -> contains_tensorcollection (v i) P
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> P (v i j k)
  | _ => False
end.

Proposition blocks_contains_tensorcollection_of_blocks :
  forall e,
  no_error e blocks -> contains_tensorcollection (blocks e) (fun e => exists shp id b, e = block shp id b).
Proof.
  induction e; try (intros; apply H; reflexivity).
  - simpl in *. intros. destruct shp as [[x y] z], shp' as [[x' y'] z'].
    simpl in *. intros. exists (x',y',z'). exists (i,j,k). exists (g i j k). reflexivity.
  - simpl in *. intros. apply H. apply H0. apply H1.
  - simpl in *. intros. apply H. apply H0. apply H1. apply H2. apply H3.
Qed.

Proposition threads_contains_tensorcollection_of_threads :
  forall e,
  no_error e threads -> contains_tensorcollection (threads e) (fun e => (exists i, e = thread i) \/ (exists i, e = lthread i)).
Proof.
  induction e; try (intros; apply H; reflexivity).
  - simpl in *. intros. left. exists (w i). reflexivity.
  - simpl in *. intros. destruct shp as [[x y] z]. simpl. intros. right. exists (b i j k). reflexivity.
  - simpl in *. intros. destruct shp as [[x y] z], shp' as [[x' y'] z'].
    simpl in *. intros. right. exists (g i i0 i1 i2 j k). reflexivity.
  - simpl in *. intros. apply H. apply H0. apply H1.
  - simpl in *. intros. apply H. apply H0. apply H1. apply H2. apply H3.
Qed.

Proposition warps_contains_tensorcollection_of_warps :
  forall e f,
  no_error e (fun e => warps e f) -> contains_tensorcollection (warps e f) (fun e => exists w, e = warp w).
Proof.
  induction e; try (intros; apply H; reflexivity).
  - simpl in *. intros. destruct shp as [[x y] z], id as [[idx idy] idz]. simpl. intros.
    exists (fun i' : nat => f (idx, idy, idz, (i * Warp_size + i', j, k))). reflexivity.
  - simpl in *. intros. destruct shp as [[x y] z], shp' as [[x' y'] z']. simpl in *. intros.
    exists (fun i' : nat => f (i, i0, i1, (i2 * Warp_size + i', j, k))). reflexivity.
  - simpl in *. intros. apply H. apply H0. apply H1.
  - simpl in *. intros. apply H. apply H0. apply H1. apply H2. apply H3.
Qed.

Proposition forall_preserves_tensor_collection :
  forall e d P,
  no_error_2 e (fun e => for_all e d) -> contains_tensorcollection e P -> contains_tensorcollection (for_all e d) P.
Proof.
  induction e; try (intros; apply H; reflexivity).
  - simpl in *. intros. apply H. apply H0. apply H2. apply H1. apply H2.
  - simpl in *. intros. destruct d.
    + simpl in *. intros. apply H1. apply H2. apply H4. apply H5.
    + simpl in *. intros. apply H1. apply H3. apply H2. apply H5.
    + simpl in *. intros. apply H1. apply H3. apply H4. apply H2.
Qed.

Proposition select_preserves_tensor_collection :
  forall e d l r P,
  no_error_2 e (fun e => sub_selection e l r d) -> contains_tensorcollection e P -> contains_tensorcollection (sub_selection e l r d) P.
Proof.
  induction e; try (intros; apply H; reflexivity).
  - simpl in *. intros. apply H. apply H0. apply H2. apply H1. apply H2.
  - simpl in *. intros. destruct d.
    + simpl in *. destruct (r <=? x) eqn:E.
      * simpl. intros. apply H1.
        apply leb_correct in E. apply Nat.le_trans with (m := r - l + l).
          apply Nat.add_lt_mono_r. apply H2. assert (l <= r). destruct (r - l) eqn:E'.
          inversion H2. assert (l + S n = r).
          apply Nat.add_sub_eq_nz. intro. inversion H6. apply E'. rewrite <- H6.
          apply Nat.le_add_r. apply Nat.sub_add in H6. rewrite H6. apply E.
        apply H4.
        apply H5.
      * simpl in *. apply H0. reflexivity.
    + simpl in *. destruct (r <=? y) eqn:E.
      * simpl. intros. apply H1.
        apply H3.
        apply leb_correct in E. apply Nat.le_trans with (m := r - l + l).
          apply Nat.add_lt_mono_r. apply H2. assert (l <= r). destruct (r - l) eqn:E'.
          inversion H2. assert (l + S n = r).
          apply Nat.add_sub_eq_nz. intro. inversion H6. apply E'. rewrite <- H6.
          apply Nat.le_add_r. apply Nat.sub_add in H6. rewrite H6. apply E.
        apply H5.
      * simpl in *. apply H0. reflexivity.
    + simpl in *. destruct (r <=? z) eqn:E.
      * simpl. intros. apply H1.
          apply H3.
          apply H4.
          apply leb_correct in E. apply Nat.le_trans with (m := r - l + l).
            apply Nat.add_lt_mono_r. apply H2. assert (l <= r). destruct (r - l) eqn:E'.
            inversion H2. assert (l + S n = r).
            apply Nat.add_sub_eq_nz. intro. inversion H6. apply E'. rewrite <- H6.
            apply Nat.le_add_r. apply Nat.sub_add in H6. rewrite H6. apply E.
      * simpl in *. apply H0. reflexivity.
Qed.

Lemma impl_collection :
  forall P P', (forall e, P e -> P' e) ->
  forall e, contains_tensorcollection e P -> contains_tensorcollection e P'.
Proof.
  induction e; try (intros; exfalso; apply H0).
  - intros. simpl in *. intros. apply H0. apply H1. apply H2.
  - intros. simpl in *. intros. apply H. apply H1; assumption.
Qed.

Lemma exists_vectorprop :
  forall n (v : Vector execution_resource n),
  (forall i, i < n ->
    exists P : execution_resource -> Prop, contains_tensorcollection (v i) P) ->
    exists (Pi : Vector (execution_resource -> Prop) n), forall i, i < n -> contains_tensorcollection (v i) (Pi i).
Proof.
  induction n.
  - intros. exists (fun i e => False). intros. inversion H0.
  - intros. assert (exists P, contains_tensorcollection (v n) P). apply H. apply le_n.
    assert (exists Pi : Vector (execution_resource -> Prop) n,
        forall i : nat, i < n -> contains_tensorcollection (v i) (Pi i)).
    apply IHn. intros. apply le_S in H1. apply H. apply H1.
    destruct H0 as [P H0]. destruct H1 as [Pi H1].
    exists (fun i => if eqb i n then P else Pi i).
      intros. inversion H2. rewrite eqb_refl. apply H0.
      assert (eqb i n = false). apply eqb_correct_2. intro; subst. apply Nat.lt_irrefl in H4. apply H4.
      rewrite H5. apply H1. apply H4.
Qed.

Fixpoint Or {n : nat} (Pi : Vector (execution_resource -> Prop) n) : (execution_resource -> Prop) :=
  match n with
  | 0 => fun e => False
  | S n => fun e => Pi n e \/ Or (n := n) Pi e
end.

Lemma Or_impl :
  forall n Pi i, i < n ->
  forall e, Pi i e -> Or (n := n) Pi e.
Proof.
  induction n.
    intros. inversion H.
    intros. simpl in *. inversion H. left. subst. apply H0.
      right. apply IHn with (i := i). apply H2. apply H0.
Qed.

