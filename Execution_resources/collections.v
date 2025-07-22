
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Proposition collection_correct :
  forall a n (v : Vector execution_resource n),
      exists (m : Vector nat n), (forall i, i < n -> count a (thread_set' (v i)) (m i)) ->
      count a (thread_set' (Collection n v)) (sum m)
.
Proof.
  induction n.
    - exists (fun i => i). intros. apply empty.
    - intros. assert (exists m : Vector nat n,
        (forall i : nat, i < n -> count a (thread_set' (v i)) (m i)) ->
        count a (thread_set' (Collection n v)) (sum m)). apply IHn.
      destruct H.
      assert (exists m, count a (thread_set' (v n)) m). apply count_exists.
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
  forall a x y z (v : Tensor' execution_resource x y z),
      exists (m : Tensor' nat x y z), (forall i j k, i < x -> j < y -> k < z -> count a (thread_set' (v i j k)) (m i j k)) ->
      count a (thread_set' (TensorCollection x y z v)) (tensorsum m)
.
Proof.
  induction z.
  - exists (fun i j k => 0). simpl. intros.
    destruct x,y; try (apply empty). clear. induction x. apply empty. apply IHx.
    clear. induction x. simpl. clear. induction y. apply empty. apply IHy. simpl in *. 
    assert (forall T, zip (T := T) (buildList y (fun _ : nat => [])) = []).
      intros. clear. induction y. reflexivity. apply IHy.
    rewrite H in *. apply IHx.
  - intros. assert ( exists m : Tensor' nat x y z,
        (forall i j k : nat,
         i < x -> j < y -> k < z -> count a (thread_set' (v i j k)) (m i j k)) ->
        count a (thread_set' (TensorCollection x y z v)) (tensorsum m)). apply IHz.
    destruct H as [fz H].
    assert (Hy : exists f, (forall i j, i < x -> j < y -> count a (thread_set' (v i j z)) (f i j)) -> count a
          (zip (buildList x (fun i : nat => zip (buildList y (fun k : nat => thread_set' (v i k z))))))
          (matrixsum (x := x) (y := y) (fun i j _ : nat => f i j))). {
          clear.
          induction y.
          - exists (fun i j => 0). intros. simpl. clear. destruct x. apply empty. induction x. apply empty. apply IHx.
          - assert (Hx : exists f, (forall i, i < x -> count a (thread_set' (v i y z)) (f i)) ->
              count a (zip (buildList x (fun i : nat => thread_set' (v i y z)))) (sum (n := x) f)). {
            clear.
            induction x.
            - exists (fun i => 0). intros. apply empty.
            - assert (exists f : nat -> nat, (forall i : nat, i < x -> count a (thread_set' (v i y z)) (f i))->
              count a (zip (buildList x (fun i0 : nat => thread_set' (v i0 y z)))) (sum (n := x) f)).
              apply IHx. destruct H as [f H].
              assert (exists n, count a (thread_set' (v x y z)) n). apply count_exists.
              destruct H0.
              exists (fun i => if (eqb i x) then x0 else f i).
              intros. simpl. apply cat_count. rewrite eqb_refl. apply H0.
              assert (sum (n := x) (fun i : nat => if eqb i x then x0 else f i) = sum (n := x) f).
              apply vector_sum_eq. intros. assert (eqb i x = false). apply eqb_correct_2.
              intro. subst. apply Nat.lt_irrefl in H2. apply H2. rewrite H3. reflexivity.
              rewrite H2. apply H. intros. assert (f i = if eqb i x then x0 else f i).
              assert (eqb i x = false). apply eqb_correct_2.
              intro. subst. apply Nat.lt_irrefl in H3. apply H3. rewrite H4. reflexivity.
              rewrite H4. apply H1. apply le_S in H3. apply H3.
          } assert (exists f : nat -> nat -> nat,
          (forall i j : nat, i < x -> j < y -> count a (thread_set' (v i j z)) (f i j)) ->
            count a (zip (buildList x (fun i : nat => zip (buildList y (fun k : nat => thread_set' (v i k z))))))
          (matrixsum (x := x) (y := y) (fun i j _ : nat => f i j))). apply IHy.
          destruct Hx as [fx Hx]. destruct H as [fy Hy].
          exists (fun i j => if (eqb j y) then fx i else fy i j).
          intros. apply transpose_lemma. simpl. destruct x.
            + simpl. clear. induction y. apply empty. apply IHy.
            + rewrite eqb_refl. apply cat_count.
              * apply Hx. intros. assert (fx i = if eqb y y then fx i else fy i y).
              rewrite eqb_refl. reflexivity. rewrite H1. apply H. apply H0. apply le_n.
              * assert (matrixsum (x := S x) (y := y) (fun i j _ : nat => if eqb j y then fx i else fy i j) = matrixsum (x := S x) (y := y) (fun i j _ : nat => fy i j)).
                  clear. apply matrixsum_eq. intros. assert (eqb j y = false). apply eqb_correct_2.
                  intro. subst. apply Nat.lt_irrefl in H0. apply H0. rewrite H1. reflexivity.
                  rewrite H0. clear H0. apply transpose_lemma. apply Hy.
                  intros. assert (fy i j = if eqb j y then fx i else fy i j).
                    assert (eqb j y = false). apply eqb_correct_2.
                    intro. subst. apply Nat.lt_irrefl in H1. apply H1. rewrite H2. reflexivity.
                  rewrite H2. apply H. apply H0. apply le_S in H1. apply H1.
   }
    destruct Hy as [fy Hy].
    exists (fun i j k => if (eqb k z) then fy i j else fz i j k).
    intros. assert (
        (tensorsum (x := x) (y := y) (z := S z) (fun i j k : nat => if eqb k z then fy i j else fz i j k)) =
        (tensorsum (x := x) (y := y) (z := z) fz) + (matrixsum (y := y) (x := x) (fun i j _ => fy i j))). {
      clear. induction z.
      + destruct x,y; simpl; try reflexivity. rewrite Nat.add_0_r. reflexivity.
      + destruct x,y; try reflexivity.
        assert (tensorsum (x := S x) (y := S y) (z := S z) (fun i j k : nat => if eqb k z then fy i j else fz i j k) =
        tensorsum (x := S x) (y := S y) (z := z) fz + matrixsum (x := S x) (y := S y) (fun i j _ : nat => fy i j)).
        apply IHz with (fz := fz). simpl.
        simpl in H. symmetry. rewrite <- Nat.add_assoc. rewrite <- H.
        symmetry. clear H. clear IHz.
        rewrite eqb_refl.
        assert (eqb z (S z) = false). apply eqb_correct_2.
        intro. subst. apply n_Sn in H. apply H. rewrite H.
        assert (tensorsum (x := S x) (y := S y) (z := z) (fun i j k : nat => if eqb k (S z) then fy i j else fz i j k) =
          tensorsum (x := S x) (y := S y) (z := z) (fun i j k : nat => if eqb k z then fy i j else fz i j k)).
          apply tensorsum_eq. intros.
          assert (eqb k z = false). apply eqb_correct_2.
          intro. subst. apply Nat.lt_irrefl in H2. apply H2. rewrite H3.
          assert (eqb k (S z) = false). apply eqb_correct_2.
          intro. subst. apply le_S in H2. apply Nat.lt_irrefl in H2. apply H2. rewrite H4.
          reflexivity.
        rewrite H0. rewrite Nat.add_comm.
        rewrite <- Nat.add_assoc. apply Nat.add_cancel_l.
        rewrite Nat.add_comm. reflexivity.
   } rewrite H1. simpl.
   assert (count a (zip (buildList x (fun i : nat =>
            zip (buildList y (fun j : nat =>
               zip (buildList (S z) (fun k : nat => thread_set' (v i j k))))))))
                (tensorsum fz + matrixsum (x := x) (y := y) (fun i j _ : nat => fy i j))). {
        apply transpose_lemma'. apply transpose_lemma. simpl. rewrite Nat.add_comm. apply cat_count.
        + apply Hy. intros. assert (fy i j = if eqb z z then fy i j else fz i j z).
          rewrite eqb_refl. reflexivity. rewrite H4. apply H0. apply H2. apply H3. apply le_n.
        + apply transpose_lemma. apply transpose_lemma'. apply H.
        intros. assert (count a (thread_set' (v i j k)) (if eqb k z then fy i j else fz i j k)).
        apply H0. apply H2. apply H3. apply le_S in H4. apply H4.
        assert (eqb k z = false). apply eqb_correct_2.
        intro. subst. apply Nat.lt_irrefl in H4. apply H4. rewrite H6 in *. apply H5.
  } apply H2.
Qed.
