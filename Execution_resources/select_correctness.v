
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.


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


Proposition induction_step_collection_select_physical :
  forall i n v m m' d l r f,
(forall n' n0 n0', n' < n -> count i (physical_thread_set (v n') f) n0 ->
    count i (physical_thread_set (select_range (v n') l r d) f) n0' -> n0' <= n0) ->
  count i (zip (buildList n (fun i : nat => physical_thread_set (v i) f))) m
-> count i (zip (buildList n (fun i0 : nat => physical_thread_set (select_range (v i0) l r d) f))) m'
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
    count i (physical_thread_set (v n') f) n0 ->
    count i (physical_thread_set (select_range (v n') l r d) f) n0' -> n0' <= n0).
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
  no_error e (fun e => select_range e l r d) -> count i (thread_set' e) m -> count i (thread_set' (select_range e l r d)) m' -> m' <= m
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
      ++ simpl in *. inversion H2. apply le_0_n.
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
      ++ simpl in *. inversion H2. apply le_0_n.
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
      ++ simpl in *. inversion H2. apply le_0_n.
Qed.

Proposition select_error :
  forall e l r d,
  select_range e l r d = Error -> (
  (exists s i b, e = block s i b) \/
  (exists s s' g, e = grid s s' g) \/
  (exists w, e = warp w) \/
  (exists i, e = thread i) \/
  (exists i, e = lthread i) \/
  e = Error \/
  (d = _x /\ exists x y z v, e = TensorCollection x y z v /\ ~(r <= x)) \/
  (d = _y /\ exists x y z v, e = TensorCollection x y z v /\ ~(r <= y)) \/
  (d = _z /\ exists x y z v, e = TensorCollection x y z v /\ ~(r <= z))
).
Proof.
  destruct e; intros; simpl in *.
  - right. right. right. left. exists t. reflexivity.
  - right. right. right. right. left. exists t. reflexivity.
  - right. right. left. exists w. reflexivity.
  - left. exists shp,id,b. reflexivity.
  - right. left. exists shp,shp',g. reflexivity.
  - inversion H.
  - destruct d.
    + destruct (r <=? x) eqn:E. inversion H.
      right. right. right. right. right. right. left.
      split. reflexivity.
      exists x,y,z,content. split.
      reflexivity.
      intro. assert (forall a b, a <= b -> a <=? b = true). {
        clear.
        induction a.
        * intros. reflexivity.
        * intros. destruct b. inversion H. simpl. apply le_S_n in H. apply IHa in H. apply H.
    } apply H1 in H0. rewrite E in H0. inversion H0.
    + destruct (r <=? y) eqn:E. inversion H.
      right. right. right. right. right. right. right. left.
      split. reflexivity.
      exists x,y,z,content. split.
      reflexivity.
      intro. assert (forall a b, a <= b -> a <=? b = true). {
        clear.
        induction a.
        * intros. reflexivity.
        * intros. destruct b. inversion H. simpl. apply le_S_n in H. apply IHa in H. apply H.
    } apply H1 in H0. rewrite E in H0. inversion H0.
    + destruct (r <=? z) eqn:E. inversion H.
      right. right. right. right. right. right. right. right.
      split. reflexivity.
      exists x,y,z,content. split.
      reflexivity.
      intro. assert (forall a b, a <= b -> a <=? b = true). {
        clear.
        induction a.
        * intros. reflexivity.
        * intros. destruct b. inversion H. simpl. apply le_S_n in H. apply IHa in H. apply H.
    } apply H1 in H0. rewrite E in H0. inversion H0.
  - right. right. right. right. right. left. reflexivity.
Qed.

Proposition select_correct_physical :
  forall i e d m m' l r f,
  no_error e (fun e => select_range e l r d) -> count i (physical_thread_set e f) m -> count i (physical_thread_set (select_range e l r d) f) m' -> m' <= m
.
Proof.
  induction e;intros; try (exfalso; apply H; reflexivity).
  - simpl in *. apply induction_step_collection_select_physical with (f := f) (i := i) (v := content) (n := n) (m := m) (m' := m') (l := l) (r := r) (d := d).
    intros. apply H with (l := l) (n := n') (d := d) (r := r) (f := f). apply H0. apply H3. apply H4.
    apply H5. apply H1. apply H2.
  - destruct d.
    + simpl in *. destruct (r <=? x) eqn:E.
      ++ simpl in *. apply leb_correct in E.
      apply zip_buildlist_inclusion with (f := (fun i : nat =>
              zip
                (buildList y
                   (fun j : nat =>
                    zip (buildList z (fun k : nat => physical_thread_set (content i j k) f)))) ++ []))
        (a := l) (m := m) (m' := m') (i := i)
      in E.
      apply E. apply H2.
      clear H2. clear E. clear H0. clear H.
      generalize dependent m. induction x.
      * intros. apply H1.
      * intros. simpl in *. rewrite cat_empty. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H3]]]]; subst.
      apply cat_count. apply H1. apply IHx. apply H2.
      ++ simpl in *. inversion H2. apply le_0_n.
    + simpl in *. destruct (r <=? y) eqn:E.
      ++ simpl in *. apply leb_correct in E.
      apply zip_buildlist_inclusion with (f := (fun i : nat =>
              zip
                (buildList x
                   (fun i0 : nat =>
                    zip (buildList z (fun k : nat => physical_thread_set (content i0 i k) f)) ++ []))))
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
      ++ simpl in *. inversion H2. apply le_0_n.
    + simpl in *. destruct (r <=? z) eqn:E.
      ++ simpl in *. apply leb_correct in E.
      apply zip_buildlist_inclusion with (f := (fun i : nat =>
              zip
                (buildList x
                   (fun i0 : nat =>
                    zip (buildList y (fun j : nat => physical_thread_set (content i0 j i) f ++ []))))))
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
      ++ simpl in *. inversion H2. apply le_0_n.
Qed.

