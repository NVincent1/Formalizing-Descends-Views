
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Fixpoint select_no_error (e : execution_resource) (l r : nat) (d : dimension): Prop :=
  match e with
  | Collection n v => forall i, i < n -> (select_no_error (v i) l r d)
  | _ => select_range e l r d <> Error
end.


Proposition induction_step_collection_select :
  forall i n v m m' d l r,
(forall n' n0 n0', n' < n -> count i (thread_set' (v n')) n0 ->
    count i (thread_set' (select_range (v n') l r d)) n0' -> n0' <= n0) ->
  count i (zip (buildList n (fun i : nat => thread_set' (v i)))) m
-> count i (zip (buildList n (fun i0 : nat => thread_set' (select_range (v i0) l r d)))) m'
-> m' <= m.
Proof.
  induction n.
  + intros. inversion H1. apply le_0_n.
  + intros. simpl in *.
  apply cat_count_rev in H0.
  apply cat_count_rev in H1.
  destruct H1 as [m1' [m2' [H0' [H1' H2']]]]. subst.
  destruct H0 as [m1 [m2 [H0 [H1 H2]]]]. subst.
  assert (forall n' n0 n0' : nat,
    n' < n ->
    count i (thread_set' (v n')) n0 ->
    count i (thread_set' (select_range (v n') l r d)) n0' -> n0' <= n0).
    intros. apply le_S in H2. apply H with (n0 := n0) (n0' := n0')in H2.
    apply H2. apply H3. apply H4.
  apply H with (n0 := m1) in H0'.
  apply IHn with (m := m2) (m' := m2') (l := l) (r := r) (d := d) in H2.
  apply Nat.add_le_mono. apply H0'. apply H2.
  apply H1. apply H1'.
  apply le_n. apply H0.
Qed.

Proposition select_correct :
  forall i e d m m' l r,
  select_no_error e l r d -> count i (thread_set' e) m -> count i (thread_set' (select_range e l r d)) m' -> m' <= m
.
Proof.
  induction e;intros; try (exfalso; apply H; reflexivity).
  - simpl in *. apply induction_step_collection_select with (i := i) (v := content) (n := n) (m := m) (m' := m') (l := l) (r := r) (d := d).
    intros. apply H with (l := l) (n := n') (d := d) (r := r). apply H0. apply H3. apply H4.
    apply H5. apply H1. apply H2.
  - destruct d.
    + simpl in *. destruct (r <=? x) eqn:E.
      ++ simpl in *. apply leb_correct in E.
      apply zip_buildlist_inclusion with (f := (fun i : nat =>
              zip
                (buildList y
                   (fun j : nat =>
                    zip (buildList z (fun k : nat => thread_set' (content i j k))))) ++ []))
        (a := l) (m := m) (m' := m') (i := i)
      in E.
      apply E. apply H2.
      clear H2. clear E. clear H0. clear H.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. rewrite cat_empty. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. apply H1. apply IHx. apply H2.
      ++ simpl in *. exfalso. apply H0. reflexivity.
    + simpl in *. destruct (r <=? y) eqn:E.
      ++ simpl in *. apply leb_correct in E.
      apply zip_buildlist_inclusion with (f := (fun i : nat =>
              zip
                (buildList x
                   (fun i0 : nat =>
                    zip (buildList z (fun k : nat => thread_set' (content i0 i k))) ++ []))))
        (a := l) (m := m) (m' := m') (i := i)
      in E.
      apply E. apply H2.
      apply transpose_lemma.
      clear H2. clear E. clear H0. clear H.
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
      ++ simpl in *. exfalso. apply H0. reflexivity.
    + simpl in *. destruct (r <=? z) eqn:E.
      ++ simpl in *. apply leb_correct in E.
      apply zip_buildlist_inclusion with (f := (fun i : nat =>
              zip
                (buildList x
                   (fun i0 : nat =>
                    zip (buildList y (fun j : nat => thread_set' (content i0 j i) ++ []))))))
        (a := l) (m := m) (m' := m') (i := i)
      in E.
      apply E. apply H2.
      apply transpose_lemma.
      apply transpose_lemma'.
      clear H2. clear E. clear H0. clear H.
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
      ++ simpl in *. exfalso. apply H0. reflexivity.
Qed.

