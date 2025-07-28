
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import blocks.
From Views.Execution_resources Require Import grids.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Theorem physical_thread_correct :
  (** Correctness of physical_thread_set for all execution resources except warps and threads :
    for an injective indices translation function, it preserves the indices in the set of logical threads *)
  forall f, (forall x y, f x = f y -> x = y) ->
  forall a e n, not_physical e -> count a (logical_thread_set e) n -> count (f a) (physical_thread_set e f) n.
Proof.
  induction e; intros; simpl in *.
  - exfalso. destruct H0. apply (H2 t). reflexivity.
  - inversion H1; inversion H6; subst. apply cons_eq. apply empty. apply cons_neq. apply empty.
    intro. apply H in H2. subst. apply Hneq. reflexivity.
  - destruct H0. exfalso. apply (H0 w). reflexivity.
  - destruct shp as [[x y] z]. apply map_injection. apply H. apply H1.
  - destruct shp as [[x y] z]. apply map_injection. apply H. apply H1.
  - assert (forall i n v n0 f,
          (forall n' n0, n' < n ->
                count i (logical_thread_set (v n')) n0 ->
                count (f i) (physical_thread_set (v n') f) n0) ->
            count i (logical_thread_set (Collection n v)) n0 ->
            count (f i) (physical_thread_set (Collection n v) f) n0). {
      clear. induction n.
      - intros. simpl in *.  inversion H0; subst. apply empty.
      - intros. simpl in *. apply cat_count_rev in H0.
      destruct H0 as [m [m' [H0 [H1 H2]]]]; subst. apply cat_count. apply H.
      apply le_n. apply H0. apply IHn. intros. apply H. apply le_S in H2. apply H2. apply H3.
      apply H1.
    } apply H3. intros n' n1 Hn. apply H0.
    apply H1. apply Hn. apply H2.
  - assert (forall a x y z v n f,
          (forall i j k n, i < x -> j < y -> k < z ->
                count a (logical_thread_set (v i j k)) n ->
                count (f a) (physical_thread_set (v i j k) f) n) ->
            count a (logical_thread_set (TensorCollection x y z v)) n ->
            count (f a) (physical_thread_set (TensorCollection x y z v) f) n). {
        clear.
        induction x.
        + intros. inversion H0; subst; apply empty.
        + intros. simpl in *.
          apply cat_count_rev in H0.
          destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
          apply cat_count. clear H1. clear IHx.
          generalize dependent m. induction y.
          - intros. inversion H0; subst; apply empty.
          - intros. simpl in *. apply cat_count_rev in H0.
            destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
            apply cat_count. clear H1. clear IHy.
            generalize dependent m0. induction z.
            * intros. inversion H0; subst; apply empty.
            * intros. simpl in *. apply cat_count_rev in H0.
              destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
              apply cat_count. apply H. apply le_n. apply le_n. apply le_n.
              apply H0. apply IHz. intros. apply H.
              apply H2. apply H3. apply le_S in H4. apply H4. apply H5.
              apply H1.
          * apply IHy. intros. apply H.
          apply H2. apply le_S in H3. apply H3. apply H4. apply H5.
          apply H1.
        - apply IHx. intros. apply H.
        apply le_S in H2. apply H2. apply H3. apply H4. apply H5.
        apply H1.
      } apply H3. intros i j k n0 Hi Hj Hk. apply H0.
      apply H1. apply Hi. apply Hj. apply Hk. apply H2.
  - inversion H1; subst; apply empty.
Qed.

Proposition physical_thread_correct_on_threads :
  forall f i, physical_thread_set (thread i) f = i :: [].
Proof. reflexivity. Qed.

Proposition physical_thread_correct_on_warps :
  forall f w, physical_thread_set (warp w) f = buildList Warp_size w.
Proof. reflexivity. Qed.

Proposition warp_correct_block :
  (** e.warps for e = block< XYZ<x, y, z> > behaves as if x was the next multiple of Warp_size
    (e.g. : 64 for x = 60 and Warp_size = 32) *)
  forall x y z idx idy idz,
  let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
  let b' := block (next_multiple x Warp_size,y,z) (idx,idy,idz) (build_block (next_multiple x Warp_size,y,z) (idx,idy,idz)) in
  forall i n (f f' : ThreadId_t -> PhysicalId_t), Warp_size <> 0 ->
  count i (physical_thread_set (warps b f) f') n ->
  count i (physical_thread_set b' f) n.
Proof.
  intros. assert (H':exists k, x = k*Warp_size + (x mod Warp_size)). apply mod_decomposition.
  destruct H' as [k H']. simpl in *.  clear b. clear b'.
  rewrite H' in *. clear H'. 
  generalize dependent n. induction k.
  - intros. destruct (x mod Warp_size) eqn:E.
    + subst; simpl in *. rewrite next_multiple_0 in H0.
      rewrite Nat.Div0.div_0_l in H0. simpl in H0. rewrite next_multiple_0.
      apply H0.
    + simpl in *. subst.
      assert (x mod Warp_size < Warp_size). apply Nat.mod_upper_bound. apply H.
      rewrite E in H1.
      assert (next_multiple (0*Warp_size + (S n0)) Warp_size = Warp_size).
      rewrite next_multiple_is_a_multiple. rewrite Nat.mul_1_l. reflexivity.
      apply H1. apply le_n_S. apply le_0_n.
      simpl in H2. rewrite H2 in *. rewrite Nat.div_same in *.
      simpl in *. rewrite cat_empty in *.
      apply transpose_lemma'2 in H0.
      apply transpose_lemma in H0.
      clear E. clear H1. clear H2.
      clear n0. clear H.
      assert (forall T f, map f (B := T)
     (thread_set_3xyz Warp_size y z (fun x : ThreadId_t => x :: [])
        (fun i0 j k : nat => (idx, idy, idz, (i0, j, k)))) = (zip
          (buildList Warp_size
             (fun i : nat =>
              zip
                (buildList y
                   (fun j : nat =>
                    buildList z
                      (fun j0 : nat =>
                       f (idx, idy, idz, (i, j, j0))))))))). {
          clear H0.
          generalize dependent y.
          generalize dependent z.
          induction Warp_size.
          - intros. reflexivity.
          - intros. simpl in *.
            destruct y,z.
            + simpl in *. clear. induction n0. reflexivity. apply IHn0.
            + simpl in *. clear. induction n0. reflexivity. apply IHn0.
            + simpl in *. clear. assert (forall T, zip (buildList y (fun _ : nat => Nil T)) = []).
            induction y. reflexivity. apply IHy.  rewrite H.  induction n0. reflexivity. apply IHn0.
            + simpl in *.
            rewrite block_ok_z.
            rewrite block_ok_yz.
            rewrite map_cat. rewrite map_cat.
            rewrite map_buildlist.
            assert (forall T f, map (B := T)
            f
            (zip
               (buildList y
                  (fun j : nat => buildList (S z) (fun k : nat => (idx, idy, idz, (n0, j, k)))))) =
              zip
            (buildList y
               (fun j : nat =>
                buildList (S z)
                     (fun j0 : nat =>
                      f (idx, idy, idz, (n0, j, j0)))))).
                {
                  intros. rewrite map_zip_buildlist. simpl.
                  clear. induction y.
                  reflexivity. simpl. rewrite map_buildlist. rewrite IHy. reflexivity.
            }
            rewrite H. clear H. simpl.
            rewrite IHn0. reflexivity.
      } rewrite H. simpl.
      clear H. assert (next_multiple (1*Warp_size) Warp_size = 1*Warp_size). apply next_multiple_unchange_multiple.
      apply H0.
      apply H.
  - intros. simpl in *.
    destruct (x mod Warp_size) eqn:E.
    + simpl in *. rewrite Nat.add_0_r in *.
      assert (next_multiple (S k * Warp_size) Warp_size = S k * Warp_size). apply next_multiple_unchange_multiple.
      simpl in H1. rewrite H1 in *. clear H1.
      assert (next_multiple (k * Warp_size) Warp_size = k * Warp_size). apply next_multiple_unchange_multiple.
      simpl in H1. rewrite H1 in *. clear H1.
      assert ((S k * Warp_size) / Warp_size = S k). apply Nat.div_mul. apply H.
      simpl in H1. rewrite H1 in *. clear H1.
      assert ((k * Warp_size) / Warp_size = k). apply Nat.div_mul. apply H.
      simpl in H1. rewrite H1 in *. clear H1.
      simpl in H0. apply cat_count_rev in H0.
      destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
      apply IHk in H1.
      rewrite Nat.add_comm.
      apply expand_block.
      apply transpose_lemma'2 in H0.
      apply transpose_lemma in H0.
      split. rewrite block_ok_xyz.
      assert (forall b, map f
       (zip
          (buildList Warp_size
             (fun i0 : nat =>
              zip
                (buildList y
                   (fun j : nat =>
                    buildList z (fun k0 : nat => b i0 j k0))))))
        = zip
            (buildList Warp_size
               (fun i : nat =>
                zip
                  (buildList y
                     (fun j : nat =>
                      buildList z (fun j0 : nat => f (b i j j0))))))).
        {
          clear. intros.
          rewrite map_zip_buildlist.
          induction Warp_size.
          - reflexivity.
          - simpl. rewrite IHn.
          assert (map f (zip (buildList y (fun j : nat => buildList z (fun k0 : nat => b n j k0))))
          = zip (buildList y (fun j : nat => buildList z (fun j0 : nat => f (b n j j0))))).
            {
              clear.
              rewrite map_zip_buildlist.
              induction y. reflexivity.
              simpl. rewrite IHy.
              rewrite map_buildlist. reflexivity.
            }
          rewrite H. reflexivity.
        }
        rewrite H2. apply H0.
        apply H1.
    + simpl in *. assert (x mod Warp_size < Warp_size). apply Nat.mod_upper_bound. apply H.
      rewrite E in H1.
      assert (next_multiple (S k * Warp_size + S n0) Warp_size = S (S k) * Warp_size). apply next_multiple_is_a_multiple.
      apply H1. apply le_n_S. apply le_0_n.
      simpl in H2. rewrite H2 in *. clear H2.
      assert (next_multiple (k * Warp_size + S n0) Warp_size = S k * Warp_size). apply next_multiple_is_a_multiple.
      apply H1. apply le_n_S. apply le_0_n.
      simpl in H2. rewrite H2 in *. clear H2.
      assert ((S (S k) * Warp_size) / Warp_size = S (S k)). apply Nat.div_mul. apply H.
      simpl in H2. rewrite H2 in *. clear H2.
      assert ((S k * Warp_size) / Warp_size = S k). apply Nat.div_mul. apply H.
      simpl in H2. rewrite H2 in *. clear H2.
      clear H1. clear E. clear n0.
      simpl in H0. apply cat_count_rev in H0.
      destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
      apply IHk in H1.
      assert (Warp_size + (Warp_size + k * Warp_size) = (S k * Warp_size) + Warp_size).
        rewrite Nat.add_comm. reflexivity.
        rewrite H2. clear H2.
      apply expand_block.
      apply transpose_lemma'2 in H0.
      apply transpose_lemma in H0.
      split. rewrite block_ok_xyz.
      assert (forall b, map f
       (zip
          (buildList Warp_size
             (fun i0 : nat =>
              zip
                (buildList y
                   (fun j : nat =>
                    buildList z (fun k0 : nat => b i0 j k0))))))
        = zip
            (buildList Warp_size
               (fun i : nat =>
                zip
                  (buildList y
                     (fun j : nat =>
                      buildList z (fun j0 : nat => f (b i j j0))))))).
        {
          clear. intros.
          rewrite map_zip_buildlist.
          induction Warp_size.
          - reflexivity.
          - simpl. rewrite IHn.
          assert (map f (zip (buildList y (fun j : nat => buildList z (fun k0 : nat => b n j k0))))
          = zip (buildList y (fun j : nat => buildList z (fun j0 : nat => f (b n j j0))))).
            {
              clear.
              rewrite map_zip_buildlist.
              induction y. reflexivity.
              simpl. rewrite IHy.
              rewrite map_buildlist. reflexivity.
            }
          rewrite H. reflexivity.
        }
        rewrite H2. apply H0.
        apply H1.
Qed.

Proposition warp_correct_grid :
  (** e.warps for e = grid< XYZ<x, y, z>, XYZ<x', y', z'> > behaves as if x' was the next multiple of Warp_size
    (e.g. : 64 for x' = 60 and Warp_size = 32)
    (x' is the size of the blocks inside the grid)
*)
  forall x y z x' y' z',
  let g := grid (x,y,z) (x',y',z') (build_grid (x,y,z) (x',y',z')) in
  let g' := grid (x,y,z) (next_multiple x' Warp_size,y',z') (build_grid (x,y,z) (next_multiple x' Warp_size,y',z')) in
  forall i n (f f' : ThreadId_t -> PhysicalId_t), Warp_size <> 0 ->
  count i (physical_thread_set (warps g f) f') n ->
  count i (physical_thread_set g' f) n.
Proof.
  induction x.
  - intros. apply H0.
  - intros. simpl in *.
    clear g. clear g'.
    destruct y,z.
      + simpl in *. clear IHx. clear f. clear f'. clear H.
        induction x. apply H0. apply IHx. apply H0.
      + simpl in *. clear IHx. clear f. clear f'. clear H.
        induction x. apply H0. apply IHx. apply H0.
      + simpl in *. clear IHx. clear f. clear f'. clear H.
        assert (forall T, zip (T := T) (buildList y (fun _ : nat => [])) = []).
            clear. induction y. reflexivity. apply IHy.
        rewrite H in H0. induction x. apply H0. apply IHx. apply H0.
      + apply cat_count_rev in H0.
        destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
        apply IHx in H1. clear IHx.
        repeat (rewrite map_cat).
        apply cat_count.
          * clear H1.
            rewrite grid_ok_z.
            rewrite grid_ok_yz.
            simpl in H0.
            apply cat_count_rev in H0.
            destruct H0 as [m1 [m2 [H0 [H2 H']]]]. subst.
            apply cat_count_rev in H0.
            destruct H0 as [m3 [m4 [H0 [H1 H']]]]. subst.
            apply cat_count. apply cat_count.
            ++ apply warp_correct_block with (f' := f').
              apply H.
              apply H0.
            ++  clear H0.
                rewrite map_zip_buildlist.
                clear H2.
                generalize dependent m4. induction z.
                --  intros. apply H1.
                --  intros. simpl in H1.
                    apply cat_count_rev in H1.
                    destruct H1 as [m1' [m2' [H1 [H2 H']]]]. subst.
                    simpl. apply cat_count. apply warp_correct_block with (f' := f'). apply H. apply H1.
                    apply IHz. apply H2.
            ++  clear H1. clear H0. 
                rewrite map_zip_buildlist.
                generalize dependent m2. induction y.
                -- intros. apply H2.
                -- intros. simpl in H2.
                    apply cat_count_rev in H2.
                    destruct H2 as [m1' [m2' [H2 [H3 H']]]]. subst.
                    apply cat_count.
                      clear IHy. clear H3. simpl in *.
                      apply cat_count_rev in H2.
                      destruct H2 as [m3' [m4' [H2 [H3 H']]]]. subst.
                      rewrite map_cat. apply cat_count.
                      apply warp_correct_block with (f' := f'). apply H. apply H2.
                      clear H2. generalize dependent m4'.
                      induction z.
                          intros. apply H3.
                          intros. simpl in *.
                          apply cat_count_rev in H3.
                          destruct H3 as [m1'' [m2'' [H3 [H4 H']]]]. subst.
                          rewrite map_cat. apply cat_count. apply warp_correct_block with (f' := f'). apply H. apply H3.
                          apply IHz. apply H4.
                     apply IHy. apply H3.
        * apply H1.
        * apply f.
        * apply H.
Qed.

Proposition blocks_correct :
  (** e.blocks conserves the same set of threads *)
  forall i e m,
  no_error e blocks -> count i (logical_thread_set e) m -> count i (logical_thread_set (blocks e)) m
.
Proof.
  induction e; intros; try (exfalso; apply H; reflexivity).
  - destruct shp as [[x y] z], shp' as [[x' y'] z']. simpl in *.
    rewrite grid_ok_xyz in H0. apply H0.
  - simpl in *. assert (forall i n v n0,
          (forall n' n0, n' < n ->
                count i (logical_thread_set (v n')) n0 ->
                count i (logical_thread_set (blocks (v n'))) n0) ->
            count i (zip (buildList n (fun i : nat => logical_thread_set (v i)))) n0 ->
            count i (zip (buildList n (fun i0 : nat => logical_thread_set (blocks (v i0))))) n0). {
        clear.
        induction n.
        + intros. apply H0.
        + intros. simpl in *.
        apply cat_count_rev in H0.
        destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
        apply cat_count.
        apply H. apply le_n. apply H0.
        apply IHn. intros. apply le_S in H2. apply H with (n0 := n0) in H2. apply H2. apply H3.
        apply H1.
    }
    apply H2. intros.
    apply H with (n := n') (m := n0) in H0.
    apply H0. apply H3. apply H4. apply H1.
  - simpl in *. assert (forall a x y z v n,
          (forall i j k n, i < x -> j < y -> k < z ->
                count a (logical_thread_set (v i j k)) n ->
                count a (logical_thread_set (blocks (v i j k))) n) ->
            count a (logical_thread_set (TensorCollection x y z v)) n ->
            count a (logical_thread_set (blocks (TensorCollection x y z v))) n). {
        clear.
        induction x.
        + intros. apply H0.
        + intros. simpl in *.
          apply cat_count_rev in H0.
          destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
          apply cat_count. clear H1. clear IHx.
          generalize dependent m. induction y.
          - intros. apply H0.
          - intros. simpl in *. apply cat_count_rev in H0.
            destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
            apply cat_count. clear H1. clear IHy.
            generalize dependent m0. induction z.
            * intros. apply H0.
            * intros. simpl in *. apply cat_count_rev in H0.
              destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
              apply cat_count. apply H. apply le_n. apply le_n. apply le_n.
              apply H0. apply IHz. intros. apply H.
              apply H2. apply H3. apply le_S in H4. apply H4. apply H5.
              apply H1.
          * apply IHy. intros. apply H.
          apply H2. apply le_S in H3. apply H3. apply H4. apply H5.
          apply H1.
        - apply IHx. intros. apply H.
        apply le_S in H2. apply H2. apply H3. apply H4. apply H5.
        apply H1.
    }
    apply H2. intros.
    apply (H i0 j k) with (m := n) in H0.
    apply H0. apply H3. apply H4. apply H5. apply H6. apply H1.
Qed.


Proposition blocks_correct_physical :
  (** e.blocks conserves the same set of physical threads *)
  forall i e m f,
  no_error e blocks -> count i (physical_thread_set e f) m -> count i (physical_thread_set (blocks e) f) m
.
Proof.
  induction e; intros; try (exfalso; apply H; reflexivity).
  - destruct shp as [[x y] z], shp' as [[x' y'] z']. simpl in *.
    rewrite grid_ok_xyz in H0.
    clear H. generalize dependent m. induction x.
    + intros. apply H0.
    + intros. simpl in *.
      rewrite map_cat in H0. apply cat_count_rev in H0.
      destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
      apply cat_count. clear H1. clear IHx.
      generalize dependent m0. induction y.
      * intros. apply H0.
      * intros. simpl in *.
        rewrite map_cat in H0. apply cat_count_rev in H0.
        destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
        apply cat_count. clear H1. clear IHy.
        generalize dependent m1. induction z.
        --  intros. apply H0.
        --  intros. simpl in *.
            rewrite map_cat in H0. apply cat_count_rev in H0.
            destruct H0 as [m2 [m2' [H0 [H1 H2]]]]. subst.
            apply cat_count. apply H0. apply IHz. apply H1.
      -- apply IHy. apply H1.
    * apply IHx. apply H1.
  - simpl in *. assert (forall i n v n0,
          (forall n' n0, n' < n ->
                count i (physical_thread_set (v n') f) n0 ->
                count i (physical_thread_set (blocks (v n')) f) n0) ->
            count i (zip (buildList n (fun i : nat => physical_thread_set (v i) f))) n0 ->
            count i (zip (buildList n (fun i0 : nat => physical_thread_set (blocks (v i0)) f))) n0). {
        clear.
        induction n.
        + intros. apply H0.
        + intros. simpl in *.
        apply cat_count_rev in H0.
        destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
        apply cat_count.
        apply H. apply le_n. apply H0.
        apply IHn. intros. apply le_S in H2. apply H with (n0 := n0) in H2. apply H2. apply H3.
        apply H1.
    }
    apply H2. intros.
    apply H with (n := n') (m := n0) (f := f) in H0.
    apply H0. apply H3. apply H4. apply H1.
  - simpl in *. assert (forall a x y z v n,
          (forall i j k n, i < x -> j < y -> k < z ->
                count a (physical_thread_set (v i j k) f) n ->
                count a (physical_thread_set (blocks (v i j k)) f) n) ->
            count a (physical_thread_set (TensorCollection x y z v) f) n ->
            count a (physical_thread_set (blocks (TensorCollection x y z v)) f) n). {
        clear.
        induction x.
        + intros. apply H0.
        + intros. simpl in *.
          apply cat_count_rev in H0.
          destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
          apply cat_count. clear H1. clear IHx.
          generalize dependent m. induction y.
          - intros. apply H0.
          - intros. simpl in *. apply cat_count_rev in H0.
            destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
            apply cat_count. clear H1. clear IHy.
            generalize dependent m0. induction z.
            * intros. apply H0.
            * intros. simpl in *. apply cat_count_rev in H0.
              destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
              apply cat_count. apply H. apply le_n. apply le_n. apply le_n.
              apply H0. apply IHz. intros. apply H.
              apply H2. apply H3. apply le_S in H4. apply H4. apply H5.
              apply H1.
          * apply IHy. intros. apply H.
          apply H2. apply le_S in H3. apply H3. apply H4. apply H5.
          apply H1.
        - apply IHx. intros. apply H.
        apply le_S in H2. apply H2. apply H3. apply H4. apply H5.
        apply H1.
    }
    apply H2. intros.
    apply (H i0 j k) with (m := n) (f := f) in H0.
    apply H0. apply H3. apply H4. apply H5. apply H6. apply H1.
Qed.


Proposition threads_correct :
  (** e.threads conserves the same set of threads *)
  forall i e m,
  no_error e threads -> count i (logical_thread_set e) m -> count i (logical_thread_set (threads e)) m
.
Proof.
  induction e; intros; try (exfalso; apply H; reflexivity).
  - simpl in *. clear H. induction Warp_size. apply H0. apply IHn. 
  - destruct shp as [[x y] z], id as [[idx idy] idz]. simpl in *.
    rewrite block_ok_xyz in H0.
    clear H. generalize dependent m. induction x.
    + intros. apply H0.
    + intros. simpl in *.
      apply cat_count_rev in H0.
      destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
      apply cat_count. clear H1. clear IHx.
      generalize dependent m0. induction y.
      * intros. apply H0.
      * intros. simpl in *.
        apply cat_count_rev in H0.
        destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
        apply cat_count. clear H1. clear IHy.
        generalize dependent m1. induction z.
        --  intros. apply H0.
        --  intros. simpl in *. rewrite cons_cat in H0.
            apply cat_count_rev in H0.
            destruct H0 as [m2 [m2' [H0 [H1 H2]]]]. subst.
            rewrite cons_cat.
            apply cat_count.
            apply H0.
            apply IHz. apply H1.
        -- apply IHy. apply H1.
      * apply IHx. apply H1.
  - destruct shp as [[x y] z], shp' as [[x' y'] z']. simpl in *.
    rewrite grid_ok_xyz in H0.
    clear H. generalize dependent m. induction x.
    + intros. apply H0.
    + intros. simpl in *.
      apply cat_count_rev in H0.
      destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
      apply cat_count. clear H1. clear IHx.
      generalize dependent m0. induction y.
      * intros. apply H0.
      * intros. simpl in *.
        apply cat_count_rev in H0.
        destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
        apply cat_count. clear H1. clear IHy.
        generalize dependent m1. induction z.
        --  intros. apply H0.
        --  intros. simpl in *.
            apply cat_count_rev in H0.
            destruct H0 as [m2 [m2' [H0 [H1 H2]]]]. subst.
            apply cat_count. rewrite block_ok_xyz in H0.
            clear H1. clear IHz.
            generalize dependent m2. induction x'.
            ++  intros. apply H0.
            ++  intros. simpl in *.
                apply cat_count_rev in H0.
                destruct H0 as [m3 [m3' [H0 [H1 H2]]]]. subst.
                apply cat_count. clear H1. clear IHx'.
                generalize dependent m3. induction y'.
                **  intros. apply H0.
                **  intros. simpl in *.
                    apply cat_count_rev in H0.
                    destruct H0 as [m4 [m4' [H0 [H1 H2]]]]. subst.
                    apply cat_count. clear H1. clear IHy'.
                    generalize dependent m4. induction z'.
                    --- intros. apply H0.
                    --- intros. simpl in *. rewrite cons_cat in H0.
                        apply cat_count_rev in H0.
                        destruct H0 as [m5 [m5' [H0 [H1 H2]]]]. subst.
                        rewrite cons_cat.
                        apply cat_count.
                        apply H0.
                        apply IHz'. apply H1.
                    --- apply IHy'. apply H1.
              ** apply IHx'. apply H1.
            ++ apply IHz. apply H1.
        -- apply IHy. apply H1.
      * apply IHx. apply H1.
  - simpl in *. assert (forall i n v n0,
          (forall n' n0, n' < n ->
                count i (logical_thread_set (v n')) n0 ->
                count i (logical_thread_set (threads (v n'))) n0) ->
            count i (zip (buildList n (fun i : nat => logical_thread_set (v i)))) n0 ->
            count i (zip (buildList n (fun i0 : nat => logical_thread_set (threads (v i0))))) n0). {
        clear.
        induction n.
        + intros. apply H0.
        + intros. simpl in *.
        apply cat_count_rev in H0.
        destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
        apply cat_count.
        apply H. apply le_n. apply H0.
        apply IHn. intros. apply le_S in H2. apply H with (n0 := n0) in H2. apply H2. apply H3.
        apply H1.
    }
    apply H2. intros.
    apply H with (n := n') (m := n0) in H0.
    apply H0. apply H3. apply H4. apply H1.
  - simpl in *. assert (forall a x y z v n,
          (forall i j k n, i < x -> j < y -> k < z ->
                count a (logical_thread_set (v i j k)) n ->
                count a (logical_thread_set (threads (v i j k))) n) ->
            count a (logical_thread_set (TensorCollection x y z v)) n ->
            count a (logical_thread_set (threads (TensorCollection x y z v))) n). {
        clear.
        induction x.
        + intros. apply H0.
        + intros. simpl in *.
          apply cat_count_rev in H0.
          destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
          apply cat_count. clear H1. clear IHx.
          generalize dependent m. induction y.
          - intros. apply H0.
          - intros. simpl in *. apply cat_count_rev in H0.
            destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
            apply cat_count. clear H1. clear IHy.
            generalize dependent m0. induction z.
            * intros. apply H0.
            * intros. simpl in *. apply cat_count_rev in H0.
              destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
              apply cat_count. apply H. apply le_n. apply le_n. apply le_n.
              apply H0. apply IHz. intros. apply H.
              apply H2. apply H3. apply le_S in H4. apply H4. apply H5.
              apply H1.
          * apply IHy. intros. apply H.
          apply H2. apply le_S in H3. apply H3. apply H4. apply H5.
          apply H1.
        - apply IHx. intros. apply H.
        apply le_S in H2. apply H2. apply H3. apply H4. apply H5.
        apply H1.
    }
    apply H2. intros.
    apply (H i0 j k) with (m := n) in H0.
    apply H0. apply H3. apply H4. apply H5. apply H6. apply H1.
Qed.


Proposition threads_correct_physical :
  (** e.threads conserves the same set of physical threads *)
  forall i e m f,
  no_error e threads -> count i (physical_thread_set e f) m -> count i (physical_thread_set (threads e) f) m
.
Proof.
  induction e; intros; try (exfalso; apply H; reflexivity).
  - simpl in *. clear H.
    generalize dependent m. induction Warp_size.
    + intros. apply H0.
    + intros. simpl in *. rewrite cons_cat. rewrite cons_cat in H0.
      apply cat_count_rev in H0.
      destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
      apply cat_count.
      apply H0.
      apply IHn. apply H1.
  - destruct shp as [[x y] z], id as [[idx idy] idz]. simpl in *.
    rewrite block_ok_xyz in H0.
    clear H. generalize dependent m. induction x.
    + intros. apply H0.
    + intros. simpl in *. rewrite map_cat in H0.
      apply cat_count_rev in H0.
      destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
      apply cat_count. clear H1. clear IHx.
      generalize dependent m0. induction y.
      * intros. apply H0.
      * intros. simpl in *. rewrite map_cat in H0.
        apply cat_count_rev in H0.
        destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
        apply cat_count. clear H1. clear IHy.
        generalize dependent m1. induction z.
        --  intros. apply H0.
        --  intros. simpl in *. rewrite cons_cat in H0.
            apply cat_count_rev in H0.
            destruct H0 as [m2 [m2' [H0 [H1 H2]]]]. subst.
            rewrite cons_cat.
            apply cat_count.
            apply H0.
            apply IHz. apply H1.
        -- apply IHy. apply H1.
      * apply IHx. apply H1.
  - destruct shp as [[x y] z], shp' as [[x' y'] z']. simpl in *.
    rewrite grid_ok_xyz in H0.
    clear H. generalize dependent m. induction x.
    + intros. apply H0.
    + intros. simpl in *. rewrite map_cat in H0.
      apply cat_count_rev in H0.
      destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
      apply cat_count. clear H1. clear IHx.
      generalize dependent m0. induction y.
      * intros. apply H0.
      * intros. simpl in *. rewrite map_cat in H0.
        apply cat_count_rev in H0.
        destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
        apply cat_count. clear H1. clear IHy.
        generalize dependent m1. induction z.
        --  intros. apply H0.
        --  intros. simpl in *. rewrite map_cat in H0.
            apply cat_count_rev in H0.
            destruct H0 as [m2 [m2' [H0 [H1 H2]]]]. subst.
            apply cat_count. rewrite block_ok_xyz in H0.
            clear H1. clear IHz.
            generalize dependent m2. induction x'.
            ++  intros. apply H0.
            ++  intros. simpl in *. rewrite map_cat in H0.
                apply cat_count_rev in H0.
                destruct H0 as [m3 [m3' [H0 [H1 H2]]]]. subst.
                apply cat_count. clear H1. clear IHx'.
                generalize dependent m3. induction y'.
                **  intros. apply H0.
                **  intros. simpl in *. rewrite map_cat in H0.
                    apply cat_count_rev in H0.
                    destruct H0 as [m4 [m4' [H0 [H1 H2]]]]. subst.
                    apply cat_count. clear H1. clear IHy'.
                    generalize dependent m4. induction z'.
                    --- intros. apply H0.
                    --- intros. simpl in *. rewrite cons_cat in H0.
                        apply cat_count_rev in H0.
                        destruct H0 as [m5 [m5' [H0 [H1 H2]]]]. subst.
                        rewrite cons_cat.
                        apply cat_count.
                        apply H0.
                        apply IHz'. apply H1.
                    --- apply IHy'. apply H1.
              ** apply IHx'. apply H1.
            ++ apply IHz. apply H1.
        -- apply IHy. apply H1.
      * apply IHx. apply H1.
  - simpl in *. assert (forall i n v n0 f,
          (forall n' n0, n' < n ->
                count i (physical_thread_set (v n') f) n0 ->
                count i (physical_thread_set (threads (v n')) f) n0) ->
            count i (zip (buildList n (fun i : nat => physical_thread_set (v i) f))) n0 ->
            count i (zip (buildList n (fun i0 : nat => physical_thread_set (threads (v i0)) f))) n0). {
        clear.
        induction n.
        + intros. apply H0.
        + intros. simpl in *.
        apply cat_count_rev in H0.
        destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
        apply cat_count.
        apply H. apply le_n. apply H0.
        apply IHn. intros. apply le_S in H2. apply H with (n0 := n0) in H2. apply H2. apply H3.
        apply H1.
    }
    apply H2. intros.
    apply H with (n := n') (m := n0) (f := f) in H0.
    apply H0. apply H3. apply H4. apply H1.
  - simpl in *. assert (forall a x y z v n f,
          (forall i j k n, i < x -> j < y -> k < z ->
                count a (physical_thread_set (v i j k) f) n ->
                count a (physical_thread_set (threads (v i j k)) f) n) ->
            count a (physical_thread_set (TensorCollection x y z v) f) n ->
            count a (physical_thread_set (threads (TensorCollection x y z v)) f) n). {
        clear.
        induction x.
        + intros. apply H0.
        + intros. simpl in *.
          apply cat_count_rev in H0.
          destruct H0 as [m [m' [H0 [H1 H2]]]]. subst.
          apply cat_count. clear H1. clear IHx.
          generalize dependent m. induction y.
          - intros. apply H0.
          - intros. simpl in *. apply cat_count_rev in H0.
            destruct H0 as [m0 [m0' [H0 [H1 H2]]]]. subst.
            apply cat_count. clear H1. clear IHy.
            generalize dependent m0. induction z.
            * intros. apply H0.
            * intros. simpl in *. apply cat_count_rev in H0.
              destruct H0 as [m1 [m1' [H0 [H1 H2]]]]. subst.
              apply cat_count. apply H. apply le_n. apply le_n. apply le_n.
              apply H0. apply IHz. intros. apply H.
              apply H2. apply H3. apply le_S in H4. apply H4. apply H5.
              apply H1.
          * apply IHy. intros. apply H.
          apply H2. apply le_S in H3. apply H3. apply H4. apply H5.
          apply H1.
        - apply IHx. intros. apply H.
        apply le_S in H2. apply H2. apply H3. apply H4. apply H5.
        apply H1.
    }
    apply H2. intros.
    apply (H i0 j k) with (m := n) (f := f) in H0.
    apply H0. apply H3. apply H4. apply H5. apply H6. apply H1.
Qed.

Fixpoint has_block (e : execution_resource) : Prop :=
  (** True iff e is a block, a grid, or a collection of blocks/grids *)
  match e with
  | Collection n v => forall i, i < n -> has_block (v i)
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> has_block (v i j k)
  | block shp id b => True
  | grid shp shp' g => True
  | _ => False
end.

Fixpoint contain_threads (e : execution_resource) : Prop :=
  (** True iff e is a warp, a block, a grid, or a collection of warps/blocks/grids *)
  match e with
  | Collection n v => forall i, i < n -> contain_threads (v i)
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> contain_threads (v i j k)
  | block shp id b => True
  | grid shp shp' g => True
  | warp w => True
  | _ => False
end.

Fixpoint has_grid (e : execution_resource) : Prop :=
  (** True iff e is a grid, or a collection of grids *)
  match e with
  | Collection n v => forall i, i < n -> has_grid (v i)
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> has_grid (v i j k)
  | grid shp shp' g => True
  | _ => False
end.

Proposition warps_no_error_case :
 (** e.warps produces a valid output iff e is a grid or a block (or a collection of grid or blocks) *)
  forall e f,
  has_block e <-> no_error e (fun e => warps e f).
Proof.
  split.
  * induction e; try (intros; exfalso; destruct H; apply H).
    - intros. simpl in *. destruct shp as [[x y] z]. destruct id as [[idx idy] idz].
      intro. inversion H0.
    - intros. simpl in *. destruct shp as [[x y] z]. destruct shp' as [[x' y'] z'].
      intro. inversion H0.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0. apply H1.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0; assumption.

  * induction e; try (intros; exfalso; apply H; reflexivity).
    - intros. simpl in *. destruct shp as [[x y] z]. destruct id as [[idx idy] idz].
      apply I.
    - intros. simpl in *. destruct shp as [[x y] z]. destruct shp' as [[x' y'] z'].
      apply I.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0. apply H1.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0; assumption.
Qed.

Proposition threads_no_error_case :
 (** e.threads produces a valid output iff e is a warp, a block or a grid (or a collection of warps/blocks/grids) *)
  forall e,
  contain_threads e <-> no_error e threads.
Proof.
  split.
  * induction e; try (intros; exfalso; destruct H; apply H).
    - intros. simpl in *. intro. inversion H0.
    - intros. simpl in *. destruct shp as [[x y] z]. destruct id as [[idx idy] idz].
      intro. inversion H0.
    - intros. simpl in *. destruct shp as [[x y] z]. destruct shp' as [[x' y'] z'].
      intro. inversion H0.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0. apply H1.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0; assumption.

  * induction e; try (intros; exfalso; apply H; reflexivity).
    - intros. apply I.
    - intros. simpl in *. destruct shp as [[x y] z]. destruct id as [[idx idy] idz].
      apply I.
    - intros. simpl in *. destruct shp as [[x y] z]. destruct shp' as [[x' y'] z'].
      apply I.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0. apply H1.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0; assumption.
Qed.

Proposition blocks_no_error_case :
  (** e.blocks produces a valid output iff e is a grid or a collection of grids *)
  forall e,
  has_grid e <-> no_error e blocks.
Proof.
  split.
  * induction e; try (intros; exfalso; destruct H; apply H).
    - intros. simpl in *. destruct shp as [[x y] z]. destruct shp' as [[x' y'] z'].
      intro. inversion H0.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0. apply H1.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0; assumption.

  * induction e; try (intros; exfalso; apply H; reflexivity).
    - intros. simpl in *. destruct shp as [[x y] z]. destruct shp' as [[x' y'] z'].
      apply I.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0. apply H1.
    - intros. simpl. intros. apply H. simpl in H0.
      apply H0; assumption.
Qed.















