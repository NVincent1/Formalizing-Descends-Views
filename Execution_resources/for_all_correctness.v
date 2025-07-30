
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
From Views.Execution_resources Require Import collections.
Require Import PeanoNat.

Proposition induction_step_collection_forall :
  forall i n v n0 d,
(forall n' n0, n' < n -> count i (logical_thread_set (v n')) n0 ->
    count i (logical_thread_set (for_all (v n') d)) n0) ->
  count i (zip (buildList n (fun i : nat => logical_thread_set (v i)))) n0
-> count i (zip (buildList n (fun i0 : nat => logical_thread_set (for_all (v i0) d))))
  n0.
Proof.
  induction n.
  + intros. apply H0.
  + intros. simpl in *.
  apply cat_count_rev in H0.
  destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
  apply cat_count.
  apply H. apply le_n. apply H0.
  apply IHn. intros. apply le_S in H2. apply H with (n0 := n0) in H2. apply H2. apply H3.
  apply H1.
Qed.

Proposition induction_step_collection_forall_physical :
  forall i n v n0 d f,
(forall n' n0, n' < n -> count i (physical_thread_set (v n') f) n0 ->
    count i (physical_thread_set (for_all (v n') d) f) n0) ->
  count i (zip (buildList n (fun i : nat => physical_thread_set (v i) f))) n0
-> count i (zip (buildList n (fun i0 : nat => physical_thread_set (for_all (v i0) d) f)))
  n0.
Proof.
  induction n.
  + intros. apply H0.
  + intros. simpl in *.
  apply cat_count_rev in H0.
  destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
  apply cat_count.
  apply H. apply le_n. apply H0.
  apply IHn. intros. apply le_S in H2. apply H with (n0 := n0) in H2. apply H2. apply H3.
  apply H1.
Qed.

Proposition for_all_correct :
  (** If e.forall(d) gives a valid output, then it preserves the number of logical threads *)
  forall i e d m,
  no_error_w_tensors e (fun e => for_all e d) -> count i (logical_thread_set e) m -> count i (logical_thread_set (for_all e d)) m
.
Proof.
  induction e; intros; try (exfalso; apply H; reflexivity).
  - simpl in *.
    apply induction_step_collection_forall.
    intros.
    apply H with (m := n0).
    apply H0. apply H2. apply H3. apply H1.
  - destruct d.
    + simpl in *. clear H. clear H0.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. rewrite cat_empty. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. apply H1. apply IHx. apply H2.
    + simpl in *. apply transpose_lemma_xy_zip. clear H. clear H0.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. clear H2. clear IHx.
        generalize dependent m1. induction y. intros.
            apply H1. intros. apply cat_count_rev in H1.
        destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
        apply cat_count. rewrite cat_empty. apply H1. apply IHy.
        apply H2.
      apply IHx. apply H2.
    + simpl in *. apply transpose_lemma_xy_zip. apply transpose_lemma_yz_zip. clear H. clear H0.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. clear H2. clear IHx.
        generalize dependent m1. induction y. intros.
          apply H1. intros. apply cat_count_rev in H1.
          destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
          apply cat_count. clear H2. clear IHy.
          generalize dependent m1'. induction z. intros.
            apply H1. intros. apply cat_count_rev in H1.
            destruct H1 as [m1'' [m2'' [H1 [H2 H3]]]]; subst.
            apply cat_count. rewrite cat_empty. apply H1. apply IHz.
            apply H2.
        apply IHy. apply H2.
      apply IHx. apply H2.
Qed.

Proposition for_all_correct_physical :
  (** If e.forall(d) gives a valid output, then it preserves the number of physical threads *)
  forall i e d m f,
  no_error_w_tensors e (fun e => for_all e d) -> count i (physical_thread_set e f) m -> count i (physical_thread_set (for_all e d) f) m
.
Proof.
  induction e; intros;simpl in *; try (exfalso; apply H; reflexivity).
  - apply induction_step_collection_forall_physical. intros.
    apply H with (n := n') (m := n0) (f := f) in H0.
    apply H0. apply H2. apply H3. apply H1.
  - destruct d.
    + simpl in *. clear H. clear H0.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. rewrite cat_empty. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. apply H1. apply IHx. apply H2.
    + simpl in *. apply transpose_lemma_xy_zip. clear H. clear H0.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. clear H2. clear IHx.
        generalize dependent m1. induction y. intros.
            apply H1. intros. apply cat_count_rev in H1.
        destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
        apply cat_count. rewrite cat_empty. apply H1. apply IHy.
        apply H2.
      apply IHx. apply H2.
    + simpl in *. apply transpose_lemma_xy_zip. apply transpose_lemma_yz_zip. clear H. clear H0.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. clear H2. clear IHx.
        generalize dependent m1. induction y. intros.
          apply H1. intros. apply cat_count_rev in H1.
          destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
          apply cat_count. clear H2. clear IHy.
          generalize dependent m1'. induction z. intros.
            apply H1. intros. apply cat_count_rev in H1.
            destruct H1 as [m1'' [m2'' [H1 [H2 H3]]]]; subst.
            apply cat_count. rewrite cat_empty. apply H1. apply IHz.
            apply H2.
        apply IHy. apply H2.
      apply IHx. apply H2.
Qed.

Proposition forall_no_error_case :
  (** e.forall(d) gives a valid output iff e is a tensor collection of execution_resources
(or a collection of tensors) *)
  forall e d,
    (exists P, contains_tensorcollection e P) <->
    no_error_w_tensors e (fun e => for_all e d)
.
Proof.
  split.
  * induction e; try (intros; exfalso; destruct H; apply H).
    - intros. simpl in *. destruct H0 as [P H0].
      intros. apply H. exists P.
      apply H0. apply H1.
    - intros. destruct H0 as [P H0]. simpl in *.
      destruct d; intro H'; inversion H'.
  * induction e; try (intros; exfalso; apply H; reflexivity).
    - intros. simpl in *.
      assert (exists (Pi : Vector (execution_resource -> Prop) n), forall i, i < n -> contains_tensorcollection (content i) (Pi i)).
        apply exists_vectorprop. intros. apply H. apply H0. apply H1.
      destruct H1 as [Pi H1]. exists (Or Pi).
      intros. apply impl_collection with (P := Pi i). apply Or_impl.
      apply H2. apply H1. apply H2.
    - intros. simpl in *. exists (fun e => e = e). intros. reflexivity.
Qed.

