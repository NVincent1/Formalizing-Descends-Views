
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Fixpoint forall_no_error (e : execution_resource) (d : dimension) : Prop :=
  match e with
  | Collection n v => forall i, i < n -> (forall_no_error (v i) d)
  | _ => for_all e d <> Error
end.

Proposition induction_step_collection_forall :
  forall i n v n0 d,
(forall n' n0, n' < n -> count i (thread_set' (v n')) n0 ->
    count i (thread_set' (for_all (v n') d)) n0) ->
  count i (zip (buildList n (fun i : nat => thread_set' (v i)))) n0
-> count i (zip (buildList n (fun i0 : nat => thread_set' (for_all (v i0) d))))
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
  forall i e d m,
  forall_no_error e d -> count i (thread_set' e) m -> count i (thread_set' (for_all e d)) m
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
    + simpl in *. apply transpose_lemma. clear H. clear H0.
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
    + simpl in *. apply transpose_lemma. apply transpose_lemma'. clear H. clear H0.
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

Proposition for_all_error :
  forall e d,
  for_all e d = Error -> (
  (exists s i b, e = block s i b) \/
  (exists s s' g, e = grid s s' g) \/
  (exists w, e = warp w) \/
  (exists i, e = thread i) \/
  (exists i, e = lthread i) \/
  e = Error
).
Proof.
  destruct e; intros; simpl in *.
  - right. right. right. left. exists t. reflexivity.
  - right. right. right. right. left. exists t. reflexivity.
  - right. right. left. exists w. reflexivity.
  - left. exists shp,id,b. reflexivity.
  - right. left. exists shp,shp',g. reflexivity.
  - inversion H.
  - destruct d;inversion H.
  - right. right. right. right. right. reflexivity.
Qed.

Proposition for_all_correct_physical :
  forall i e d m f,
  forall_no_error e d -> count i (physical_thread_set e f) m -> count i (physical_thread_set (for_all e d) f) m
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
    + simpl in *. apply transpose_lemma. clear H. clear H0.
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
    + simpl in *. apply transpose_lemma. apply transpose_lemma'. clear H. clear H0.
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

