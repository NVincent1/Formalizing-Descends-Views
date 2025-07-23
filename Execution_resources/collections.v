
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
