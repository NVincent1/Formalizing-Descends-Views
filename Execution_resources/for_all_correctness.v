
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

Lemma forall_block_x :
  forall x y z i n b, count i (thread_set_3xyz x y z (fun x : ThreadId_t => x :: []) b) n ->
            count i (zip (buildList x (fun i0 : nat => thread_set_3xyz 1 y z (fun x0 : ThreadId_t => x0 :: [])
                    (fun _ j k : nat => b i0 j k)))) n.
Proof.
  intros.
  generalize dependent n. induction x; intros. destruct y; apply H.
  simpl in *. destruct y,z.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. apply cat_count_rev with (l1 := b x y z
    :: (thread_set_1z (S x) (S y) z (fun x : ThreadId_t => x :: []) b) ++
    thread_set_2yz (S x) y (S z) (fun x : ThreadId_t => x :: []) b) in H.
    destruct H as [m1 [m2 [H [H' H2]]]]. subst.
    apply cat_count with (l1 := b x y z
        :: ((thread_set_1z 1 (S y) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
        thread_set_2yz 1 y (S z) (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k)) ++ [])).
    rewrite block_ok_yz.
    rewrite block_ok_yz in H.
    apply cat_count_rev with (l1 := b x y z
    :: thread_set_1z (S x) (S y) z (fun x : ThreadId_t => x :: []) b) in H.
    destruct H as [m1' [m2' [H [H1 H2]]]]. subst.
    rewrite cat_empty.
    apply cat_count with (l1 := b x y z
    :: thread_set_1z 1 (S y) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k)).
    rewrite block_ok_z. rewrite block_ok_z in H.
    apply H.
    simpl.
    clear H. clear H'. clear IHx. generalize dependent m2'. induction y.
        intros. apply H1. simpl. intros.
        apply cat_count_rev with (l1 := b x y z
        :: buildList z (fun k : nat => b x y k)) in H1.
        destruct H1 as [m [m' [H1 [H2 H3]]]]. subst.
        apply cat_count with (l1 := b x y z
        :: buildList z (fun k : nat => b x y k)).
        apply H1. apply IHy. apply H2.
    apply IHx in H'.
    apply H'.
Qed.

Lemma forall_block_y :
  forall x y z i n b, count i (thread_set_3xyz x y z (fun x : ThreadId_t => x :: []) b) n ->
            count i (zip (buildList y (fun i0 : nat => thread_set_3xyz x 1 z (fun x0 : ThreadId_t => x0 :: [])
                    (fun i1 _ k : nat => b i1 i0 k)))) n.
Proof.
  intros. apply transpose_xy_block in H.
  generalize dependent n. induction y; intros. destruct x; apply H.
  simpl in *. destruct x,z.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. apply cat_count_rev with (l1 := b x y z
    :: (thread_set_1z (S x) (S y) z (fun x : ThreadId_t => x :: []) b) ++
    thread_set_2xz x (S y) (S z) (fun x : ThreadId_t => x :: []) b) in H.
    destruct H as [m1 [m2 [H [H' H2]]]]. subst.
    apply cat_count with (l1 := b x y z
    :: ((thread_set_1z (S x) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i1 _ k : nat => b i1 y k) ++ []) ++
    thread_set_3xyz x 1 (S z) (fun x0 : ThreadId_t => x0 :: []) (fun i1 _ k : nat => b i1 y k))).
    rewrite block_ok_xyz.
    rewrite block_ok_xz in H.
    apply cat_count_rev with (l1 := b x y z
    :: thread_set_1z (S x) (S y) z (fun x : ThreadId_t => x :: []) b) in H.
    destruct H as [m1' [m2' [H [H1 H2]]]]. subst.
    rewrite cat_empty.
    apply cat_count with (l1 := b x y z
    :: thread_set_1z (S x) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i1 _ k : nat => b i1 y k)).
    rewrite block_ok_z. rewrite block_ok_z in H.
    apply H.
    simpl.
    assert (forall z, zip (buildList x (fun i0 : nat =>
        zip (buildList 1 (fun _ : nat => buildList (S z) (fun k : nat => b i0 y k))))) =
        zip (buildList x (fun j : nat => buildList (S z) (fun k : nat => b j y k)))).
        clear. induction x.
        reflexivity. simpl. intros.
        simpl in IHx. rewrite IHx.
        rewrite cat_empty. reflexivity.
    simpl in H0.
    rewrite H0. apply H1.
    apply IHy in H'.
    apply H'.
Qed.

Lemma forall_block_z :
  forall x y z i n b, count i (thread_set_3xyz x y z (fun x : ThreadId_t => x :: []) b) n ->
            count i (zip (buildList z
           (fun i0 : nat => thread_set_3xyz x y 1 (fun x0 : ThreadId_t => x0 :: [])
                    (fun i1 j k : nat => b i1 j i0)))) n.
Proof.
intros. apply transpose_xz_block in H.
generalize dependent n. induction z; intros. destruct x,y; apply H.
simpl in *. destruct x,y.
  simpl in *. rewrite blockempty. apply H. reflexivity.
  simpl in *. rewrite blockempty. apply H. reflexivity.
  simpl in *. rewrite blockempty. apply H. reflexivity.
  simpl in *. apply cat_count_rev with (l1 := b x y z
  :: (thread_set_1y (S x) y (S z) (fun x : ThreadId_t => x :: []) b) ++
  thread_set_2xy x (S y) (S z) (fun x : ThreadId_t => x :: []) b) in H.
  destruct H as [m1 [m2 [H [H' H2]]]]. subst.
  apply cat_count with (l1 := b x y z
  :: (thread_set_2yz (S x) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i1 j _ : nat => b i1 j z) ++
  thread_set_3xyz x (S y) 1 (fun x0 : ThreadId_t => x0 :: []) (fun i1 j _ : nat => b i1 j z))).
  rewrite block_ok_xyz.
  rewrite block_ok_xy in H.
  apply cat_count_rev with (l1 := b x y z
  :: thread_set_1y (S x) y (S z) (fun x : ThreadId_t => x :: []) b) in H.
  destruct H as [m1' [m2' [H [H1 H2]]]]. subst.
  apply cat_count with (l1 := b x y z
  :: thread_set_2yz (S x) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i1 j k : nat => b i1 j z)).
  rewrite block_ok_yz. rewrite block_ok_y in H.
  simpl.
  assert (forall n, count i (b x y z :: buildList y (fun k : nat => b x k z)) n ->
  count i (b x y z :: zip (buildList y (fun j : nat => b x j z :: []))) n).
    clear. induction y. intros. apply H. intros. simpl in *. inversion H; clear H; subst.
    apply cons_eq; apply IHy; apply H4.
    apply cons_neq. apply IHy; apply H4. apply Hneq.
  apply H0 in H.
  apply H.
  simpl.
  assert (forall n, count i (zip (buildList x (fun j : nat => buildList (S y) (fun k : nat => b j k z)))) n ->
  count i (zip (buildList x (fun i0 : nat => zip (buildList (S y) (fun j : nat => b i0 j z :: []))))) n).
    clear. induction x. intros. apply H. intros. simpl in *. inversion H; clear H; subst.
    apply cons_eq. rewrite zip_ok. apply cat_count_rev in H4.
    destruct H4 as [m [m' [H1 [H2 H3]]]]. subst.
    apply cat_count.
    apply H1. apply IHx; apply H2.
    apply cons_neq.
    rewrite zip_ok. apply cat_count_rev in H4.
    destruct H4 as [m [m' [H1 [H2 H3]]]]. subst.
    apply cat_count.
    apply H1. apply IHx; apply H2. apply Hneq.
  apply H0 in H1.
  apply H1.
  apply IHz in H'.
  apply H'.
Qed.

Lemma forall_grid_x :
  forall x y z x' y' z' i n g, count i (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n ->
            count i (zip (buildList x (fun i0 : nat => thread_set_3xyz 1 y z (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b)
                    (fun _ j k : nat => g i0 j k)))) n.
Proof.
  intros.
  generalize dependent n. induction x; intros. destruct y; apply H.
  simpl in *. destruct y,z.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *.
    apply cat_count_rev in H.
    destruct H as [m01 [m02 [H [H01 H02]]]]. subst.
    apply cat_count_rev in H.
    destruct H as [m11 [m12 [H [H11 H12]]]]. subst.
    apply cat_count_rev in H.
    destruct H as [m21 [m22 [H [H21 H2]]]]. subst.
    repeat (rewrite cat_empty).
    apply cat_count.
    apply cat_count.
    apply cat_count.
    apply H.
    rewrite grid_ok_z.
    rewrite grid_ok_z in H21.
    apply H21.
    rewrite grid_ok_yz.
    rewrite grid_ok_yz in H11.
    apply H11.
    clear H. clear H11. clear H21. clear IHx. generalize dependent m02. induction x.
        intros. apply H01. simpl. intros.
        apply cat_count_rev in H01.
        destruct H01 as [m [m' [H1 [H2 H3]]]]. subst.
        repeat (rewrite cat_empty).
        apply cat_count.
        rewrite grid_ok_z in H1.
        rewrite grid_ok_yz in H1.
        rewrite grid_ok_z.
        rewrite grid_ok_yz.
        apply H1. apply IHx.
    apply H2.
Qed.

Lemma forall_grid_y :
  forall x y z x' y' z' i n g, count i (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n ->
            count i (zip (buildList y (fun i0 : nat => thread_set_3xyz x 1 z (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b)
                    (fun i1 _ k : nat => g i1 i0 k)))) n.
Proof.
  intros. apply transpose_xy_grid in H.
  generalize dependent n. induction y; intros. destruct x; apply H.
  simpl in *. destruct x,z.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *.
    apply cat_count_rev in H.
    destruct H as [m01 [m02 [H [H01 H02]]]]. subst.
    apply cat_count_rev in H.
    destruct H as [m11 [m12 [H [H11 H12]]]]. subst.
    apply cat_count_rev in H.
    destruct H as [m21 [m22 [H [H21 H2]]]]. subst.
    repeat (rewrite cat_empty).
    apply cat_count.
    apply cat_count.
    apply cat_count.
    apply H.
    rewrite grid_ok_z.
    rewrite grid_ok_z in H21.
    apply H21.
    rewrite grid_ok_xyz.
    rewrite grid_ok_xz in H11.
    clear H. clear H01. clear H21. clear IHy. generalize dependent m12. induction x.
        intros. apply H11. simpl. intros.
        apply cat_count_rev in H11.
        destruct H11 as [m [m' [H1 [H2 H3]]]]. subst.
        repeat (rewrite cat_empty).
        apply cat_count. apply H1.
        apply IHx. apply H2.
    clear H. clear H11. clear H21. clear IHy. generalize dependent m02. induction y.
        intros. apply H01. simpl. intros.
        apply cat_count_rev in H01.
        destruct H01 as [m [m' [H1 [H2 H3]]]]. subst.
        repeat (rewrite cat_empty).
        apply cat_count.
        rewrite grid_ok_z in H1.
        rewrite grid_ok_xz in H1.
        rewrite grid_ok_z.
        rewrite grid_ok_xyz.
        apply cat_count_rev in H1.
        destruct H1 as [m1 [m2 [H1 [H2' H3]]]]. subst.
        repeat (rewrite cat_empty).
        apply cat_count.
        apply H1.
        apply cat_count_rev in H1.
        destruct H1 as [m1' [m2' [H1 [H2'' H3]]]]. subst.
        repeat (rewrite cat_empty).
        clear H2. clear H2''. clear H1. clear IHy.
        clear m12. clear m21. clear m'. clear m1'. clear m2'.
        generalize dependent m2. induction x.
          intros. apply H2'.
          intros. simpl in *.
          apply cat_count_rev in H2'.
          destruct H2' as [m01 [m02 [H [H01 H02]]]]. subst.
          apply cat_count_rev in H.
          destruct H as [m11 [m12 [H [H11 H12]]]]. subst.
          repeat (rewrite cat_empty).
          apply cat_count. apply cat_count.
          apply H.
          apply H11.
          apply IHx. apply H01.
    apply IHy.
    apply H2.
Qed.

Lemma forall_grid_z :
  forall x y z x' y' z' i n g, count i (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n ->
            count i (zip (buildList z (fun i0 : nat => thread_set_3xyz x y 1 (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b)
                    (fun i j k : nat => g i j i0)))) n.
Proof.
  intros. apply transpose_xz_grid in H.
  generalize dependent n. induction z; intros. destruct x,y; apply H.
  simpl in *. destruct x,y.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *. rewrite blockempty. apply H. reflexivity.
    simpl in *.
    apply cat_count_rev in H.
    destruct H as [m01 [m02 [H [H01 H02]]]]. subst.
    apply cat_count_rev in H.
    destruct H as [m11 [m12 [H [H11 H12]]]]. subst.
    apply cat_count_rev in H.
    destruct H as [m21 [m22 [H [H21 H2]]]]. subst.
    repeat (rewrite cat_empty).
    apply cat_count.
    apply cat_count.
    apply cat_count.
    apply H.
    rewrite grid_ok_yz.
    rewrite grid_ok_y in H21.
    clear H. clear H11. clear H01. clear IHz. generalize dependent m22.
    clear m02. clear m12. induction y.
      intros. apply H21.
      intros. simpl in *.
      apply cat_count_rev in H21.
      destruct H21 as [m01 [m02 [H [H01 H02]]]]. subst.
      repeat (rewrite cat_empty).
      apply cat_count.
      apply H.
      apply IHy. apply H01.
    rewrite grid_ok_xyz.
    rewrite grid_ok_xy in H11.
    clear H. clear H21. clear H01. clear IHz. generalize dependent m12.
    clear m02. clear m22. induction x.
      intros. apply H11.
      intros. simpl in *.
      apply cat_count_rev in H11.
      destruct H11 as [m01 [m02 [H [H01 H02]]]]. subst.
      apply cat_count_rev in H.
      destruct H as [m11 [m12 [H [H11 H12]]]]. subst.
      repeat (rewrite cat_empty).
      apply cat_count.
      apply cat_count.
      apply H.
      clear H01. clear H. clear IHx.
      clear m21. clear m02. clear m11. generalize dependent m12.
      induction y.
        intros. apply H11.
        intros. simpl in *.
        apply cat_count_rev in H11.
        destruct H11 as [m01 [m02 [H [H01 H02]]]]. subst.
        repeat (rewrite cat_empty).
        apply cat_count.
        apply H.
        apply IHy. apply H01.
      apply IHx. apply H01.
    clear H. clear H11. clear H21. clear IHz. generalize dependent m02.
    clear m12. clear m21. clear m22. induction z.
        intros. apply H01.
        simpl. intros.
        apply cat_count_rev in H01.
        destruct H01 as [m01 [m02' [H [H01 H02]]]]. subst.
        apply cat_count_rev in H.
        destruct H as [m11 [m12 [H [H11 H12]]]]. subst.
        apply cat_count_rev in H.
        destruct H as [m21 [m22 [H [H21 H22]]]]. subst.
        repeat (rewrite cat_empty).
        apply cat_count.
        apply cat_count.
        apply cat_count.
        apply H.
        rewrite grid_ok_y in H21.
        rewrite grid_ok_yz.
        clear H. clear H11. clear H01. clear m02'. clear m12. clear m21.
        generalize dependent m22. clear IHz. induction y.
          intros. apply H21.
          intros. simpl in *.
          apply cat_count_rev in H21.
          destruct H21 as [m01 [m02 [H [H01 H02]]]]. subst.
          repeat (rewrite cat_empty).
          apply cat_count.
          apply H.
          apply IHy. apply H01.
        rewrite grid_ok_xyz.
        rewrite grid_ok_xy in H11.
        clear H. clear H21. clear H01. clear m02'. clear m22. clear m21.
        generalize dependent m12. clear IHz. induction x.
          intros. apply H11.
          intros. simpl in *.
          apply cat_count_rev in H11.
          destruct H11 as [m01 [m02 [H [H01 H02]]]]. subst.
          apply cat_count_rev in H.
          destruct H as [m11 [m12' [H [H11 H12]]]]. subst.
          repeat (rewrite cat_empty).
          apply cat_count. apply cat_count.
          apply H.
          clear H. clear H01. clear m02. clear m11.
          generalize dependent m12'. clear IHx. induction y.
            intros. apply H11.
          intros. simpl in *.
          apply cat_count_rev in H11.
          destruct H11 as [m01 [m02 [H [H01 H02]]]]. subst.
          repeat (rewrite cat_empty).
          apply cat_count.
          apply H.
          apply IHy. apply H01.
        apply IHx. apply H01.
    apply IHz. apply H01.
Qed.

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
    destruct d; try (exfalso; apply H; reflexivity).
    simpl. clear H. induction Warp_size. apply H0. apply IHn.
  - destruct d.
    + destruct shp as [p z]. destruct p as [x y].
    destruct id as [p iz]. destruct p as [ix iy].
    destruct x,y,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct y; apply H0.
      * destruct y; destruct z; apply H0.
      * inversion H0. subst.
        destruct x. apply H0.
        simpl. clear. induction x.
        ** apply empty.
        ** simpl. apply IHx.
      * inversion H0. subst.
        destruct x. destruct z; apply H0.
        simpl. clear. induction x.
        ** destruct z; apply empty.
        ** simpl. destruct z; apply IHx.
      * inversion H0. subst.
        destruct x. destruct y; apply H0.
        simpl. clear. induction x.
        ** destruct y; apply empty.
        ** simpl. destruct y; apply IHx.
      * destruct x.
        ** exfalso; apply H. simpl. destruct y,z;try reflexivity.
        ** destruct y,z.
          -- simpl in *. rewrite block_ok_xyz in H0. apply H0.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) 1 (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
              simpl. apply H0. apply forall_block_x in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) 1 (fun x0 : ThreadId_t => x0 :: []) b) m).
              simpl. apply H0. apply forall_block_x in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
              simpl. apply H0. apply forall_block_x in H1. apply H1.
    + destruct shp as [p z]. destruct p as [x y].
    destruct id as [p iz]. destruct p as [ix iy].
    destruct y,x,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct z; apply H0.
      * inversion H0. subst.
        destruct y. apply H0.
        simpl. clear. induction y.
        ** apply empty.
        ** simpl. apply IHy.
      * inversion H0. subst.
        destruct y. destruct z; apply H0.
        simpl. clear. induction y.
        ** destruct z; apply empty.
        ** simpl. destruct z; apply IHy.
      * inversion H0. subst.
        destruct y. destruct x; apply H0.
        simpl. clear. induction y.
        ** destruct x; apply empty.
        ** simpl. destruct x; apply IHy.
      * destruct y.
        ** exfalso; apply H. simpl. destruct x,z;try reflexivity.
        ** destruct x,z.
          -- simpl in *. rewrite block_ok_yz in H0. rewrite cat_empty in H0. apply H0.
          -- simpl in *.
                assert (count i (thread_set_3xyz 1 (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
                simpl. apply H0. apply forall_block_y in H1. apply H1.
          -- simpl in *.
                assert (count i (thread_set_3xyz (S (S x)) (S (S y)) 1 (fun x0 : ThreadId_t => x0 :: []) b) m).
                simpl. apply H0. apply forall_block_y in H1. apply H1.
          -- simpl in *.
                assert (count i (thread_set_3xyz (S (S x)) (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
                simpl. apply H0. apply forall_block_y in H1. apply H1.
    + destruct shp as [p z]. destruct p as [x y].
    destruct id as [p iz]. destruct p as [ix iy].
    destruct z,x,y.
      * apply H0.
      * destruct y; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct y; apply H0.
      * inversion H0. subst.
        destruct z. apply H0.
        simpl. clear. induction z.
        ** apply empty.
        ** simpl. apply IHz.
      * inversion H0. subst.
        destruct z. destruct y; apply H0.
        simpl. clear. induction z.
        ** destruct y; apply empty.
        ** simpl. destruct y; apply IHz.
      * inversion H0. subst.
        destruct z. destruct x; apply H0.
        simpl. clear. induction z.
        ** destruct x; apply empty.
        ** simpl. destruct x; apply IHz.
      * destruct z.
        ** exfalso; apply H. simpl. destruct x,y;try reflexivity.
        ** destruct x,y.
          -- simpl in *. rewrite block_ok_z in H0. rewrite cat_empty in H0. rewrite cat_empty in H0.
          assert (forall i m, count i (buildList z (fun k : nat => b 0 0 k)) m -> count i (zip (buildList z (fun i0 : nat => b 0 0 i0 :: []))) m).
            clear. induction z. intros. apply H. simpl. intros. inversion H; clear H; subst; try (apply cons_eq); try (apply cons_neq); try (apply IHz; apply H4). apply Hneq.
          inversion H0; inversion H6; subst; clear H0; clear H6;
          repeat (repeat (apply cons_eq); try (apply cons_neq)); try (apply H1; apply H11).
          apply Hneq. apply Hneq. apply Hneq0. apply Hneq.
        -- simpl in *.
              assert (count i (thread_set_3xyz 1 (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
              simpl. apply H0. apply forall_block_z in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) 1 (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
              simpl. apply H0. apply forall_block_z in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) m).
              simpl. apply H0. apply forall_block_z in H1. apply H1.
  - destruct d.
    + destruct shp as [p z]. destruct p as [x y].
    destruct shp' as [p z']. destruct p as [x' y'].
    destruct x,y,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct y; apply H0.
      * destruct y; destruct z; apply H0.
      * inversion H0. subst.
        destruct x. apply H0.
        simpl. clear. induction x.
        ** apply empty.
        ** simpl. apply IHx.
      * inversion H0. subst.
        destruct x. destruct z; apply H0.
        simpl. clear. induction x.
        ** destruct z; apply empty.
        ** simpl. destruct z; apply IHx.
      * inversion H0. subst.
        destruct x. destruct y; apply H0.
        simpl. clear. induction x.
        ** destruct y; apply empty.
        ** simpl. destruct y; apply IHx.
      * destruct x.
        ** exfalso; apply H. simpl. destruct y,z;try reflexivity.
        ** destruct y,z.
          -- simpl in *. rewrite grid_ok_xyz in H0. repeat (rewrite block_ok_xyz in H0). repeat (rewrite block_ok_xyz).
             simpl in H0. repeat (rewrite cat_empty in H0).
             apply cat_count_rev in H0; destruct H0 as [m1 [m2 [H0 [H1 H2]]]]; subst.
             apply cat_count_rev in H1; destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
             apply cat_count. apply H0.
             apply cat_count. apply H1.
             clear H0. clear H1. clear H.
             generalize dependent m4. induction x.
                ++ intros. apply H2.
                ++ simpl in *. intros. repeat (rewrite cat_empty in H2).
                apply cat_count_rev in H2; destruct H2 as [m [m' [H0 [H1 H2]]]]; subst.
                apply cat_count. apply H0.
                apply IHx in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) 1 (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_x in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) 1 (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_x in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_x in H1. apply H1.
    + destruct shp as [p z]. destruct p as [x y].
    destruct shp' as [p z']. destruct p as [x' y'].
    destruct y,x,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct z; apply H0.
      * inversion H0. subst.
        destruct y. apply H0.
        simpl. clear. induction y.
        ** apply empty.
        ** simpl. apply IHy.
      * inversion H0. subst.
        destruct y. destruct z; apply H0.
        simpl. clear. induction y.
        ** destruct z; apply empty.
        ** simpl. destruct z; apply IHy.
      * inversion H0. subst.
        destruct y. destruct x; apply H0.
        simpl. clear. induction y.
        ** destruct x; apply empty.
        ** simpl. destruct x; apply IHy.
      * destruct y.
        ** exfalso; apply H. simpl. destruct x,z;try reflexivity.
        ** destruct x,z.
          -- simpl in *. rewrite grid_ok_yz in H0. repeat (rewrite block_ok_xyz in H0). repeat (rewrite block_ok_xyz).
             simpl in H0. repeat (rewrite cat_empty in H0).
             apply cat_count_rev in H0; destruct H0 as [m1 [m2 [H0 [H1 H2]]]]; subst.
             apply cat_count_rev in H1; destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
             apply cat_count. apply H0.
             apply cat_count. apply H1.
             clear H0. clear H1. clear H.
             generalize dependent m4. induction y.
                ++ intros. apply H2.
                ++ simpl in *. intros. repeat (rewrite cat_empty in H2).
                apply cat_count_rev in H2; destruct H2 as [m [m' [H0 [H1 H2]]]]; subst.
                apply cat_count. apply H0.
                apply IHy in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz 1 (S (S y)) (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_y in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) 1 (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_y in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_y in H1. apply H1.
    + destruct shp as [p z]. destruct p as [x y].
    destruct shp' as [p z']. destruct p as [x' y'].
    destruct z,x,y.
      * apply H0.
      * destruct y; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct y; apply H0.
      * inversion H0. subst.
        destruct z. apply H0.
        simpl. clear. induction z.
        ** apply empty.
        ** simpl. apply IHz.
      * inversion H0. subst.
        destruct z. destruct y; apply H0.
        simpl. clear. induction z.
        ** destruct y; apply empty.
        ** simpl. destruct y; apply IHz.
      * inversion H0. subst.
        destruct z. destruct x; apply H0.
        simpl. clear. induction z.
        ** destruct x; apply empty.
        ** simpl. destruct x; apply IHz.
      * destruct z.
        ** exfalso; apply H. simpl. destruct x,y;try reflexivity.
        ** destruct x,y.
          -- simpl in *. rewrite grid_ok_z in H0. repeat (rewrite block_ok_xyz in H0). repeat (rewrite block_ok_xyz).
             simpl in H0. repeat (rewrite cat_empty in H0).
             apply cat_count_rev in H0; destruct H0 as [m1 [m2 [H0 [H1 H2]]]]; subst.
             apply cat_count_rev in H1; destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
             apply cat_count. apply H0.
             apply cat_count. apply H1.
             clear H0. clear H1. clear H.
             generalize dependent m4. induction z.
                ++ intros. apply H2.
                ++ simpl in *. intros. repeat (rewrite cat_empty in H2).
                apply cat_count_rev in H2; destruct H2 as [m [m' [H0 [H1 H2]]]]; subst.
                apply cat_count. apply H0.
                apply IHz in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz 1 (S (S y)) (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_z in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) 1 (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_z in H1. apply H1.
        -- simpl in *.
              assert (count i (thread_set_3xyz (S (S x)) (S (S y)) (S (S z)) (fun b => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) m).
              simpl. apply H0. apply forall_grid_z in H1. apply H1.
  - simpl in *.
    apply induction_step_collection_forall.
    intros.
    apply H with (m := n0).
    apply H0. apply H2. apply H3. apply H1.
Qed.

Proposition for_all_error :
  forall e d,
  for_all e d = Error -> (
  (d = _x /\ exists y z i b, e = block (1,y,z) i b) \/
  (d = _x /\ exists y z i g, e = grid (1,y,z) i g) \/
  (d = _y /\ exists x z i b, e = block (x,1,z) i b) \/
  (d = _y /\ exists x z i g, e = grid (x,1,z) i g) \/
  (d = _z /\ exists x y i b, e = block (x,y,1) i b) \/
  (d = _z /\ exists x y i g, e = grid (x,y,1) i g) \/
  (d <> _x /\ exists w, e = warp w) \/
  (exists i, e = thread i) \/
  (exists i, e = lthread i) \/
  e = Error
).
Proof.
  destruct e,d; intros; simpl in *.
  - right. right. right. right. right. right. right. left. exists t. reflexivity.
  - right. right. right. right. right. right. right. left. exists t. reflexivity.
  - right. right. right. right. right. right. right. left. exists t. reflexivity.
  - right. right. right. right. right. right. right. right. left. exists t. reflexivity.
  - right. right. right. right. right. right. right. right. left. exists t. reflexivity.
  - right. right. right. right. right. right. right. right. left. exists t. reflexivity.
  - inversion H.
  - right. right. right. right. right. right. left. split. intro. inversion H0. exists w. reflexivity.
  - right. right. right. right. right. right. left. split. intro. inversion H0. exists w. reflexivity.
  - destruct shp as [p z]. destruct p as [x y].
    destruct id as [p idz]. destruct p as [idx idy]. destruct x.
      * destruct y,z; try (destruct y); try (destruct z); inversion H.
      * destruct x. destruct y,z; left; split; try (reflexivity).
        + exists 0,0, (idx,idy,idz), b;reflexivity.
        + exists 0,(S z), (idx,idy,idz), b;reflexivity.
        + exists (S y),0, (idx,idy,idz), b;reflexivity.
        + exists (S y),(S z), (idx,idy,idz), b;reflexivity.
        + destruct y,z; try (destruct y); try (destruct z); inversion H.
  - destruct shp as [p z]. destruct p as [x y].
    destruct id as [p idz]. destruct p as [idx idy]. destruct y.
      * destruct x,z; try (destruct x); try (destruct z); inversion H.
      * destruct y. destruct x,z; right; right; left; split; try (reflexivity).
        + exists 0,0, (idx,idy,idz), b;reflexivity.
        + exists 0,(S z), (idx,idy,idz), b;reflexivity.
        + exists (S x),0, (idx,idy,idz), b;reflexivity.
        + exists (S x),(S z), (idx,idy,idz), b;reflexivity.
        + destruct x,z; try (destruct x); try (destruct z); inversion H.
  - destruct shp as [p z]. destruct p as [x y].
    destruct id as [p idz]. destruct p as [idx idy]. destruct z.
      * destruct x,y; try (destruct x); try (destruct y); inversion H.
      * destruct z. destruct x,y; right; right; right; right; left; split; try (reflexivity).
        + exists 0,0, (idx,idy,idz), b;reflexivity.
        + exists 0,(S y), (idx,idy,idz), b;reflexivity.
        + exists (S x),0, (idx,idy,idz), b;reflexivity.
        + exists (S x),(S y), (idx,idy,idz), b;reflexivity.
        + destruct x,y; try (destruct x); try (destruct y); inversion H.
  - destruct shp as [p z]. destruct p as [x y].
    destruct shp' as [p z']. destruct p as [x' y']. destruct x.
      * destruct y,z; try (destruct y); try (destruct z); inversion H.
      * destruct x. destruct y,z; right; left; split; try (reflexivity).
        + exists 0,0, (x',y',z'), g;reflexivity.
        + exists 0,(S z), (x',y',z'), g;reflexivity.
        + exists (S y),0, (x',y',z'), g;reflexivity.
        + exists (S y),(S z), (x',y',z'), g;reflexivity.
        + destruct y,z; try (destruct y); try (destruct z); inversion H.
  - destruct shp as [p z]. destruct p as [x y].
    destruct shp' as [p z']. destruct p as [x' y']. destruct y.
      * destruct x,z; try (destruct x); try (destruct z); inversion H.
      * destruct y. destruct x,z; right; right; right; left; split; try (reflexivity).
        + exists 0,0, (x',y',z'), g;reflexivity.
        + exists 0,(S z), (x',y',z'), g;reflexivity.
        + exists (S x),0, (x',y',z'), g;reflexivity.
        + exists (S x),(S z), (x',y',z'), g;reflexivity.
        + destruct x,z; try (destruct x); try (destruct z); inversion H.
  - destruct shp as [p z]. destruct p as [x y].
    destruct shp' as [p z']. destruct p as [x' y']. destruct z.
      * destruct x,y; try (destruct x); try (destruct y); inversion H.
      * destruct z. destruct x,y; right; right; right; right; right; left; split; try (reflexivity).
        + exists 0,0, (x',y',z'), g;reflexivity.
        + exists 0,(S y), (x',y',z'), g;reflexivity.
        + exists (S x),0, (x',y',z'), g;reflexivity.
        + exists (S x),(S y), (x',y',z'), g;reflexivity.
        + destruct x,y; try (destruct x); try (destruct y); inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - right. right. right. right. right. right. right. right. right. reflexivity.
  - right. right. right. right. right. right. right. right. right. reflexivity.
  - right. right. right. right. right. right. right. right. right. reflexivity.
Qed.

Proposition for_all_correct_physical :
  forall i e d m f,
  forall_no_error e d -> count i (physical_thread_set e f) m -> count i (physical_thread_set (for_all e d) f) m
.
Proof.
  induction e; intros;simpl in *; try (exfalso; apply H; reflexivity).
  - destruct d.
    + simpl. clear H. generalize dependent m. induction Warp_size; intros. apply H0. simpl in *. inversion H0;subst.
    apply cons_eq. apply IHn. apply H4. apply cons_neq. apply IHn. apply H4. apply Hneq.
    + exfalso; apply H; reflexivity.
    + exfalso; apply H; reflexivity.
  - destruct shp as [[x y] z]. destruct id as [[id idy] idz]. destruct d.
    + destruct x,y,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct y; apply H0.
      * destruct y; destruct z; apply H0.
      * destruct x. apply H0. clear H. simpl. clear b. induction x. apply H0. apply IHx.
      * destruct x. destruct z; apply H0. clear H. destruct z; simpl; clear b; induction x; try apply H0; apply IHx.
      * destruct x. destruct y; apply H0. clear H. destruct y; simpl; clear b; induction x; try apply H0; apply IHx.
      * destruct x. destruct y,z; apply H0. clear H. destruct y,z; simpl; clear b; induction x; try apply H0; apply IHx.
    + destruct y,x,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct z; apply H0.
      * destruct y. apply H0. clear H. simpl. clear b. induction y. apply H0. apply IHy.
      * destruct y. destruct z; apply H0. clear H. destruct z; simpl; clear b; induction y; try apply H0; apply IHy.
      * destruct y. destruct x; apply H0. clear H. destruct x; simpl; clear b; induction y; try apply H0; apply IHy.
      * destruct y. destruct x,z; apply H0. clear H. destruct x,z; simpl; clear b; induction y; try apply H0; apply IHy.
    + destruct z,x,y.
      * apply H0.
      * destruct y; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct y; apply H0.
      * destruct z. apply H0. clear H. simpl. clear b. induction z. apply H0. apply IHz.
      * destruct z. destruct y; apply H0. clear H. destruct y; simpl; clear b; induction z; try apply H0; apply IHz.
      * destruct z. destruct x; apply H0. clear H. destruct x; simpl; clear b; induction z; try apply H0; apply IHz.
      * destruct z. destruct x,y; apply H0. clear H. destruct x,y; simpl; clear b; induction z; try apply H0; apply IHz.
  - destruct shp as [[x y] z]. destruct shp' as [[x' y'] z']. destruct d.
    + destruct x,y,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct y; apply H0.
      * destruct y; destruct z; apply H0.
      * destruct x. apply H0. clear H. simpl. clear g. induction x. apply H0. apply IHx.
      * destruct x. destruct z; apply H0. clear H. destruct z; simpl; clear g; induction x; try apply H0; apply IHx.
      * destruct x. destruct y; apply H0. clear H. destruct y; simpl; clear g; induction x; try apply H0; apply IHx.
      * destruct x. destruct y,z; apply H0. clear H. destruct y,z; simpl; clear g; induction x; try apply H0; apply IHx.
    + destruct y,x,z.
      * apply H0.
      * destruct z; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct z; apply H0.
      * destruct y. apply H0. clear H. simpl. clear g. induction y. apply H0. apply IHy.
      * destruct y. destruct z; apply H0. clear H. destruct z; simpl; clear g; induction y; try apply H0; apply IHy.
      * destruct y. destruct x; apply H0. clear H. destruct x; simpl; clear g; induction y; try apply H0; apply IHy.
      * destruct y. destruct x,z; apply H0. clear H. destruct x,z; simpl; clear g; induction y; try apply H0; apply IHy.
    + destruct z,x,y.
      * apply H0.
      * destruct y; apply H0.
      * destruct x; apply H0.
      * destruct x; destruct y; apply H0.
      * destruct z. apply H0. clear H. simpl. clear g. induction z. apply H0. apply IHz.
      * destruct z. destruct y; apply H0. clear H. destruct y; simpl; clear g; induction z; try apply H0; apply IHz.
      * destruct z. destruct x; apply H0. clear H. destruct x; simpl; clear g; induction z; try apply H0; apply IHz.
      * destruct z. destruct x,y; apply H0. clear H. destruct x,y; simpl; clear g; induction z; try apply H0; apply IHz.
  - apply induction_step_collection_forall_physical. intros.
    apply H with (n := n') (m := n0) (f := f) in H0.
    apply H0. apply H2. apply H3. apply H1.
Qed.

