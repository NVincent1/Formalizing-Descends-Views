
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
    for an injective index translation function, it preserves the indices in the set of logical threads *)
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
  (** e.warps for e = block< XYZ<x, y, z> > behaves as if e was of shape
      X< next_multiple (x*y*z) Warp_size >  *) 
  forall x y z idx idy idz,
  let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
  let b' := block (next_multiple (x*y*z) Warp_size,1,1) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
  forall i n (f f' : ThreadId_t -> PhysicalId_t), Warp_size <> 0 ->
  count i (physical_thread_set (warps b f) f') n ->
  count i (physical_thread_set b' f) n.
Proof.
  intros. assert (H':exists k, x*y*z = k*Warp_size + ((x*y*z) mod Warp_size)). apply mod_decomposition.
  destruct H' as [k H']. simpl in *.  clear b. clear b'.
  rewrite H' in *. clear H'. 
  generalize dependent n. induction k.
  - intros. destruct ((x*y*z) mod Warp_size) eqn:E.
    + subst; simpl in *. rewrite next_multiple_0_m in H0.
      rewrite Nat.Div0.div_0_l in H0. simpl in H0. rewrite next_multiple_0_m.
      apply H0.
    + simpl in *. subst.
      assert ((x*y*z) mod Warp_size < Warp_size). apply Nat.mod_upper_bound. apply H.
      rewrite E in H1.
      assert (next_multiple (0*Warp_size + (S n0)) Warp_size = Warp_size).
      rewrite next_multiple_is_a_multiple. rewrite Nat.mul_1_l. reflexivity.
      apply H1. apply le_n_S. apply le_0_n.
      simpl in H2. rewrite H2 in *. rewrite Nat.div_same in *.
      simpl in *. rewrite cat_empty in *.
      clear E. clear H1. clear H2.
      clear n0. clear H. rewrite thread_set_3xyz_correct_on_block.
      generalize dependent n. induction Warp_size.
      * intros. apply H0.
      * intros. simpl in *.
        inversion H0; subst.
        -- apply cons_eq. apply IHn. apply H4.
        -- apply cons_neq. apply IHn. apply H4. apply Hneq.
      *
      apply H.
  - intros. simpl in *.
    destruct ((x*y*z) mod Warp_size) eqn:E.
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
      split. rewrite thread_set_3xyz_correct_on_block.
      clear H1. clear IHk. clear E. clear H. simpl.
      assert (forall n, count i
       ((buildList Warp_size
           (fun i : nat => f (idx, idy, idz, (k * n + i, 0, 0))) ++ []) ++ []) m ->
        count i
        (map f
           (zip
              (buildList Warp_size
                 (fun i0 : nat => (idx, idy, idz, (k * n + i0, 0, 0)) :: [])))) m). {
          clear.
          generalize dependent m.
          induction Warp_size.
            intros. apply H.
            intros. simpl in H. simpl. inversion H; subst. simpl. apply cons_eq. apply IHn. apply H4.
            simpl. apply cons_neq. apply IHn. apply H4. apply Hneq.
      }
      apply H. apply H0.
      apply H1.
    + simpl in *. assert ((x*y*z) mod Warp_size < Warp_size). apply Nat.mod_upper_bound. apply H.
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
      split. rewrite thread_set_3xyz_correct_on_block.
      assert (forall n, count i
       ((buildList Warp_size
           (fun i : nat => f (idx, idy, idz, (S k * n + i, 0, 0))) ++ []) ++ []) m ->
        count i
        (map f
           (zip
              (buildList Warp_size
                 (fun i0 : nat => (idx, idy, idz, (S k * n + i0, 0, 0)) :: [])))) m). {
          clear.
          generalize dependent m.
          induction Warp_size.
            intros. apply H.
            intros. simpl in H. simpl. inversion H; subst. simpl. apply cons_eq. apply IHn. apply H4.
            simpl. apply cons_neq. apply IHn. apply H4. apply Hneq.
      } simpl in *. apply H2 in H0. apply H0.
        apply H1.
Qed.

Proposition warp_correct_grid :
  (** e.warps for e = grid< XYZ<x, y, z>, XYZ<x', y', z'> > behaves as if e was of shape
    <XYZ<x,y,z>, X< next_multiple (x*y*z) Warp_size > >
*)
  forall x y z x' y' z',
  let g := grid (x,y,z) (x',y',z') (build_grid (x,y,z) (x',y',z')) in
  let g' := grid (x,y,z) (next_multiple (x'*y'*z') Warp_size,1,1) (build_grid (x,y,z) (x',y',z')) in
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
            rewrite thread_set_1z_correct_on_grid.
            rewrite thread_set_2yz_correct_on_grid.
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
    rewrite thread_set_3xyz_correct_on_grid in H0. apply H0.
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
        clear. intros. simpl. apply transpose_lemma_yz_zip. apply transpose_lemma_xy_zip.
        apply transpose_lemma_yz_zip. generalize dependent n.
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
    rewrite thread_set_3xyz_correct_on_grid in H0.
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
        clear. intros. simpl. apply transpose_lemma_yz_zip. apply transpose_lemma_xy_zip.
        apply transpose_lemma_yz_zip. generalize dependent n.
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
    rewrite thread_set_3xyz_correct_on_block in H0.
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
    rewrite thread_set_3xyz_correct_on_grid in H0.
    clear H.  intros. simpl. apply transpose_lemma_yz_zip. apply transpose_lemma_xy_zip.
    apply transpose_lemma_yz_zip. generalize dependent m. induction x.
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
            apply cat_count. rewrite thread_set_3xyz_correct_on_block in H0.
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
        clear. intros. simpl. apply transpose_lemma_yz_zip. apply transpose_lemma_xy_zip.
        apply transpose_lemma_yz_zip. generalize dependent n.
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
    rewrite thread_set_3xyz_correct_on_block in H0.
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
    rewrite thread_set_3xyz_correct_on_grid in H0.
    clear H. intros. simpl. apply transpose_lemma_yz_zip. apply transpose_lemma_xy_zip.
    apply transpose_lemma_yz_zip. generalize dependent m. induction x.
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
            apply cat_count. rewrite thread_set_3xyz_correct_on_block in H0.
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
        clear. intros. simpl. apply transpose_lemma_yz_zip. apply transpose_lemma_xy_zip.
        apply transpose_lemma_yz_zip. generalize dependent n.
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

Fixpoint contains_warps (e : execution_resource) : Prop :=
  (** True iff e is a block, a grid, or a collection of blocks/grids *)
  match e with
  | Collection n v => forall i, i < n -> contains_warps (v i)
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> contains_warps (v i j k)
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

Fixpoint contains_blocks (e : execution_resource) : Prop :=
  (** True iff e is a grid, or a collection of grids *)
  match e with
  | Collection n v => forall i, i < n -> contains_blocks (v i)
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> contains_blocks (v i j k)
  | grid shp shp' g => True
  | _ => False
end.

Proposition warps_no_error_case :
 (** e.warps produces a valid output iff e is a grid or a block (or a collection of grids or blocks) *)
  forall e f,
  contains_warps e <-> no_error e (fun e => warps e f).
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
  contains_blocks e <-> no_error e blocks.
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

(** Proving that warps takes contiguous indices and the indices that we expect *)

Proposition warp_start_block :
  forall x' y' z' x y z idx idy idz f,
  let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    Warp_size <> 0 -> forall i,
      i < get_physical_id (x',y',z') (x,y,z) (idx,idy,idz,(0,0,0)) ->
    count i (physical_thread_set (warps b (get_physical_id (x',y',z') (x,y,z))) f) 0.
Proof.
  intros.
  assert (
    forall x y z idx idy idz,
    let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    let b' := block (next_multiple (x*y*z) Warp_size,1,1) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    forall i n (f f' : ThreadId_t -> PhysicalId_t), Warp_size <> 0 ->
    count i (physical_thread_set b' f) n ->
    count i (physical_thread_set (warps b f) f') n). clear. intros x y z idx idy idz b b' i n f f' H.
    apply count_impl_equiv. clear n. intro n. apply warp_correct_block. apply H.
    apply H1. apply H.
    clear H1. simpl.
    clear b. clear f.
    simpl in *. repeat (rewrite Nat.mul_0_r in *). repeat (rewrite Nat.add_0_r in *).
    assert (forall a, (get_physical_id (x', y', z') (x, y, z)) a = i -> count a (thread_set_3xyz (next_multiple (x * y * z) Warp_size) 1 1
        (fun x0 : ThreadId_t => x0 :: [])
        (fun i0 j k : nat => (idx, idy, idz, (i0, j, k)))) 0). {
      intros. destruct a as [[[x1 y1] z1] [[x2 y2] z2]]. simpl in H1.
      assert (x1 <> idx \/ x1 = idx). apply or_comm. apply excluded_middle. destruct H2 as [H2 | H2].
      apply block_not_contain_other_indices_on_xyz. left. apply H2.
      assert (y1 <> idy \/ y1 = idy). apply or_comm. apply excluded_middle. destruct H3 as [H3 | H3].
      apply block_not_contain_other_indices_on_xyz. right. left. apply H3.
      assert (z1 <> idz \/ z1 = idz). apply or_comm. apply excluded_middle. destruct H4 as [H4 | H4].
      apply block_not_contain_other_indices_on_xyz. right. right. apply H4.
      repeat (rewrite H2 in *).
      repeat (rewrite H3 in *).
      repeat (rewrite H4 in *).
      clear H2. clear H3. clear H4.
      assert (i >= idx * next_multiple (x * y * z) Warp_size +
             idy * x' * next_multiple (x * y * z) Warp_size +
             idz * x' * y' * next_multiple (x * y * z) Warp_size).
          rewrite <- H1. assert (idx * next_multiple (x * y * z) Warp_size +
idy * x' * next_multiple (x * y * z) Warp_size +
idz * x' * y' * next_multiple (x * y * z) Warp_size + x2 + x * y2 + 
x * y * z2 =
(idx * next_multiple (x * y * z) Warp_size +
idy * x' * next_multiple (x * y * z) Warp_size +
idz * x' * y' * next_multiple (x * y * z) Warp_size) + (x2 + x * y2 + 
x * y * z2)). repeat (rewrite Nat.add_assoc). reflexivity. rewrite H2. clear H2. apply Nat.le_add_r.
          exfalso. apply Nat.nle_gt in H2. apply H2. apply H0.
      }
      apply map_count_0. apply H1.
Qed.

Proposition warp_end_block :
  forall x' y' z' x y z idx idy idz f,
  let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    Warp_size <> 0 -> forall i,
      i >= get_physical_id (x',y',z') (x*y*z,1,1) (idx,idy,idz,(next_multiple (x*y*z) Warp_size,0,0)) ->
    count i (physical_thread_set (warps b (get_physical_id (x',y',z') (x,y,z))) f) 0.
Proof.
  intros. 
  assert (
    forall x y z idx idy idz,
    let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    let b' := block (next_multiple (x*y*z) Warp_size,1,1) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    forall i n (f f' : ThreadId_t -> PhysicalId_t), Warp_size <> 0 ->
    count i (physical_thread_set b' f) n ->
    count i (physical_thread_set (warps b f) f') n). clear. intros x y z idx idy idz b b' i n f f' H.
    apply count_impl_equiv. clear n. intro n. apply warp_correct_block. apply H.
    apply H1. apply H.
    clear H1. simpl.
    clear b. clear f.
    simpl in *. repeat (rewrite Nat.mul_0_r in *). repeat (rewrite Nat.add_0_r in *). repeat (rewrite Nat.mul_1_r in *).
    assert (forall a, (get_physical_id (x', y', z') (x, y, z)) a = i -> count a (thread_set_3xyz (next_multiple (x * y * z) Warp_size) 1 1
        (fun x0 : ThreadId_t => x0 :: [])
        (fun i0 j k : nat => (idx, idy, idz, (i0, j, k)))) 0). {
      intros. destruct a as [[[x1 y1] z1] [[x2 y2] z2]]. simpl in H1.
      assert (x1 <> idx \/ x1 = idx). apply or_comm. apply excluded_middle. destruct H2 as [H2 | H2].
      apply block_not_contain_other_indices_on_xyz. left. apply H2.
      assert (y1 <> idy \/ y1 = idy). apply or_comm. apply excluded_middle. destruct H3 as [H3 | H3].
      apply block_not_contain_other_indices_on_xyz. right. left. apply H3.
      assert (z1 <> idz \/ z1 = idz). apply or_comm. apply excluded_middle. destruct H4 as [H4 | H4].
      apply block_not_contain_other_indices_on_xyz. right. right. apply H4.
      repeat (rewrite H2 in *).
      repeat (rewrite H3 in *).
      repeat (rewrite H4 in *).
      clear H2. clear H3. clear H4.
      assert (x2 >= next_multiple (x * y * z) Warp_size \/ x2 < next_multiple (x * y * z) Warp_size). apply Nat.le_gt_cases. destruct H2 as [H2 | H2].
      apply block_not_contain_larger_on_xyz. left. apply H2.
      assert (y2 >= 1 \/ y2 < 1). apply Nat.le_gt_cases. destruct H3 as [H3 | H3].
      apply block_not_contain_larger_on_xyz. right. left. apply H3.
      assert (z2 >= 1 \/ z2 < 1). apply Nat.le_gt_cases. destruct H4 as [H4 | H4].
      apply block_not_contain_larger_on_xyz. right. right. apply H4.
      inversion H3; inversion H4.
      repeat (rewrite H6 in *).
      repeat (rewrite H7 in *).
      clear H3. clear H4. clear H6. clear H7.
      repeat (rewrite Nat.mul_0_r in *).
      repeat (rewrite Nat.add_0_r in *).
      assert (i < idx * next_multiple (x * y * z) Warp_size +
           idy * x' * next_multiple (x * y * z) Warp_size +
           idz * x' * y' * next_multiple (x * y * z) Warp_size +
           next_multiple (x * y * z) Warp_size).
          rewrite <- H1. apply Nat.add_lt_mono_l.
          apply H2.
          exfalso. apply Nat.nle_gt in H0. apply H0. apply H3.
          inversion H7. inversion H6. inversion H6.
      }
      apply map_count_0. apply H1.
Qed.

Proposition warp_contiguous_block :
  forall x' y' z' x y z idx idy idz f,
  let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    Warp_size <> 0 -> forall i,
      i >= get_physical_id (x',y',z') (x,y,z) (idx,idy,idz,(0,0,0)) ->
      i < get_physical_id (x',y',z') (x*y*z,1,1) (idx,idy,idz,(next_multiple (x*y*z) Warp_size,0,0)) ->
    count i (physical_thread_set (warps b (get_physical_id (x',y',z') (x,y,z))) f) 1.
Proof.
  intros.
assert (
    forall x y z idx idy idz,
    let b := block (x,y,z) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    let b' := block (next_multiple (x*y*z) Warp_size,1,1) (idx,idy,idz) (build_block (x,y,z) (idx,idy,idz)) in
    forall i n (f f' : ThreadId_t -> PhysicalId_t), Warp_size <> 0 ->
    count i (physical_thread_set b' f) n ->
    count i (physical_thread_set (warps b f) f') n). clear. intros x y z idx idy idz b b' i n f f' H.
    apply count_impl_equiv. clear n. intro n. apply warp_correct_block. apply H.
  apply H2. apply H. clear H2.
  simpl in *.
  clear b. clear f.
  repeat (rewrite Nat.mul_1_r in *).
  repeat (rewrite Nat.mul_0_r in *).
  repeat (rewrite Nat.add_0_r in *).
  set (s := idx * next_multiple (x * y * z) Warp_size +
      idy * x' * next_multiple (x * y * z) Warp_size +
      idz * x' * y' * next_multiple (x * y * z) Warp_size) in *.
  set (x1 := idx).
  set (y1 := idy).
  set (z1 := idz).
  set (x2 := i-s).
  set (y2 := 0).
  set (z2 := 0).
  assert (
          get_physical_id (x',y',z') (x,y,z) ((x1,y1,z1),(x2,y2,z2)) = i /\
          count ((x1,y1,z1),(x2,y2,z2)) (thread_set_3xyz (next_multiple (x * y * z) Warp_size) 1 1
        (fun x0 : ThreadId_t => x0 :: [])
        (fun i0 j k : nat => (idx, idy, idz, (i0, j, k)))) 1).
        simpl. assert (i = s + (i - s)).
            assert (i + (s - s) = i + s - s). apply Nat.add_sub_assoc. apply le_n.
            assert (i + s - s = s + i - s). rewrite Nat.add_comm. reflexivity. rewrite H3 in H2. clear H3.
            assert (s + i - s = s + (i - s)). symmetry. apply Nat.add_sub_assoc. apply H0.
            rewrite H3 in H2. clear H3. rewrite Nat.sub_diag in H2. rewrite Nat.add_0_r in H2. apply H2.
            assert (s + ((i - s) mod x) + x * (((i - s) / x) mod y) + x * y * (((i - s) / (x * y))) = s + (i-s)).
            rewrite <- Nat.add_assoc. rewrite <- Nat.add_assoc. apply Nat.add_cancel_l.
            assert (forall a, a < next_multiple (x * y * z) Warp_size ->
              a mod x + x*(a/x mod y) + x*y* (a/(x*y)) = a).
              clear. intros.
              rewrite Nat.div_mod_eq with (x := a) (y := x).
              assert ((x * (a / x) + a mod x) mod x = a mod x). rewrite Nat.add_comm. rewrite Nat.mul_comm.
              rewrite Nat.Div0.mod_add. apply Nat.Div0.mod_mod. rewrite H0. clear H0.
              assert (x * (((x * (a / x) + a mod x) / x) mod y) + x * y * (((x * (a / x) + a mod x) / (x * y))) = x * (a / x)).
                assert (((x * (a / x) + a mod x) / x) mod y = a / x mod y).
                rewrite Nat.mul_comm. rewrite Nat.div_add_l.
                assert (a mod x / x = 0). apply Nat.div_small.
                apply Nat.mod_upper_bound.
                intro. subst. simpl in H. rewrite next_multiple_0_m in H. inversion H.
                rewrite H0. rewrite Nat.add_0_r. reflexivity.
                intro. subst. simpl in H. rewrite next_multiple_0_m in H. inversion H.
                rewrite H0. clear H0. rewrite <- Nat.mul_assoc. rewrite <- Nat.mul_add_distr_l.
                apply Nat.mul_cancel_l.
                intro. subst. simpl in H. rewrite next_multiple_0_m in H. inversion H.
                rewrite Nat.div_mod_eq with (x := (a/x)) (y := y).
                assert ((y * (a / x / y) + (a / x) mod y) mod y = (a / x) mod y).
                  rewrite Nat.add_comm. rewrite Nat.mul_comm.
                  rewrite Nat.Div0.mod_add. apply Nat.Div0.mod_mod. rewrite H0. clear H0.
                  assert ((x * (y * (a / x / y) + (a / x) mod y) + a mod x) / (x * y) = (a / x / y)).
                    rewrite <- Nat.Div0.div_div.
                    rewrite Nat.mul_comm. rewrite Nat.div_add_l.
                    assert (a mod x / x = 0). apply Nat.div_small.
                    apply Nat.mod_upper_bound.
                    intro. subst. simpl in H. rewrite next_multiple_0_m in H. inversion H.
                    rewrite H0. rewrite Nat.add_0_r. clear H0.
                    rewrite Nat.mul_comm. rewrite Nat.div_add_l.
                    assert ((a / x) mod y / y = 0). apply Nat.div_small.
                    apply Nat.mod_upper_bound.
                    intro. subst. simpl in H. rewrite Nat.mul_0_r in H. rewrite next_multiple_0_m in H. inversion H.
                    rewrite H0. rewrite Nat.add_0_r. clear H0. reflexivity.
                    intro. subst. simpl in H. rewrite Nat.mul_0_r in H. rewrite next_multiple_0_m in H. inversion H.
                    intro. subst. simpl in H. rewrite next_multiple_0_m in H. inversion H.
                    rewrite H0. clear H0. rewrite Nat.add_comm. reflexivity.
                  rewrite <- Nat.add_assoc. rewrite H0.
                  rewrite Nat.add_comm. reflexivity.
              rewrite Nat.add_assoc.
              apply H3 with (a := (i-s)).
              assert (forall a b c, c > 0 -> a < b + c -> a - b < c). {
                clear. induction a. intros. apply H.
                intros. destruct b.
                + rewrite Nat.sub_0_r. apply H0.
                + simpl. apply IHa. apply H. apply le_S_n. rewrite <- plus_Sn_m. apply H0.
              } destruct x,y,z; simpl in H0; repeat (rewrite Nat.mul_0_r in H1); try (rewrite next_multiple_0_m in H1; rewrite Nat.add_0_r in H1).
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * exfalso. apply Nat.nle_gt in H0. apply H0. apply H1.
                 * apply H4. apply next_multiple_lt_0. simpl. apply le_n_S. apply le_0_n.
                  apply H. apply H1.
            * unfold x1, y1, z1. unfold x2, y2, z2. repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r). repeat (rewrite Nat.add_assoc). rewrite <- H2 in H3. split.
            symmetry. apply H2.
          + apply block_complete.
            assert (s + (i - s) <
              s + next_multiple (x * y * z) Warp_size).
              rewrite <- H2. apply H1.
            repeat (rewrite <- Nat.add_assoc in H4). apply Nat.add_lt_mono_l in H4.
            apply H4.
            auto. auto.
  * 
    assert (forall a, get_physical_id (x', y', z') (x, y, z) a = i ->
            a = (x1, y1, z1, (x2, y2, z2)) \/ count a
       (thread_set_3xyz (next_multiple (x * y * z) Warp_size) 1 1
          (fun x0 : ThreadId_t => x0 :: [])
          (fun i0 j k : nat => (idx, idy, idz, (i0, j, k)))) 0). {
        intros. simpl in H3. destruct a as [[[xa1 ya1] za1] [[xa2 ya2] za2]].
        clear H2.
        assert (Hx1:xa1 <> idx \/ xa1 = idx). apply or_comm. apply excluded_middle.
          destruct Hx1 as [Hx1 | Hx1]. right. apply block_not_contain_other_indices_on_xyz.
          left. apply Hx1.
        assert (Hy1:ya1 <> idy \/ ya1 = idy). apply or_comm. apply excluded_middle.
          destruct Hy1 as [Hy1 | Hy1]. right. apply block_not_contain_other_indices_on_xyz.
          right. left. apply Hy1.
        assert (Hz1:za1 <> idz \/ za1 = idz). apply or_comm. apply excluded_middle.
          destruct Hz1 as [Hz1 | Hz1]. right. apply block_not_contain_other_indices_on_xyz.
          right. right. apply Hz1.
        assert (Hx2 : xa2 >= next_multiple (x * y * z) Warp_size \/ xa2 < next_multiple (x * y * z) Warp_size).
          apply or_comm. apply Nat.lt_ge_cases. destruct Hx2 as [Hx2 | Hx2]. right. apply block_not_contain_larger_on_xyz.
          left. apply Hx2.
        assert (Hy2 : ya2 >= 1 \/ ya2 < 1).
          apply or_comm. apply Nat.lt_ge_cases. destruct Hy2 as [Hy2 | Hy2]. right. apply block_not_contain_larger_on_xyz.
          right. left. apply Hy2.
        assert (Hz2 : za2 >= 1 \/ za2 < 1).
          apply or_comm. apply Nat.lt_ge_cases. destruct Hz2 as [Hz2 | Hz2]. right. apply block_not_contain_larger_on_xyz.
          right. right. apply Hz2.
        assert (Hy2' : ya2 = 0). inversion Hy2. reflexivity. inversion H4.
        assert (Hz2' : za2 = 0). inversion Hz2. reflexivity. inversion H4.
        clear Hy2. clear Hz2.
        repeat (rewrite Hy2' in *). repeat (rewrite Hz2' in *).
        repeat (rewrite Hx1 in *). repeat (rewrite Hy1 in *). repeat (rewrite Hz1 in *).
        repeat (rewrite Nat.mul_0_r in *). repeat (rewrite Nat.add_0_r in *).
        clear Hx1. clear Hy1. clear Hz1. clear Hy2'. clear Hz2'. clear xa1.
        clear ya1. clear za1. clear ya2. clear za2.
        unfold x1,y1,z1 in *. clear x1. clear y1. clear z1.
        unfold y2,z2 in *. clear y2. clear z2.
        assert (i - s = xa2).
        unfold s. rewrite <- H3. rewrite Nat.add_comm.
          rewrite Nat.add_sub. reflexivity.
          unfold x2. rewrite <- H2. left. reflexivity.
    }
    clear H0. assert
    (count i (map (get_physical_id (x', y', z') (x, y, z)) (thread_set_3xyz (next_multiple (x * y * z) Warp_size) 1 1
          (fun x0 : ThreadId_t => x0 :: [])
          (fun i0 j k : nat => (idx, idy, idz, (i0, j, k))))) 1).
    apply map_count_1 with (X := (x1,y1,z1,(x2,y2,z2))).
    destruct H2. apply H0. destruct H2. apply H2. apply H3.
    apply H0.
Qed.

Proposition warp_end_grid :
  forall x' y' z' x y z f,
  let g := grid (x,y,z) (x',y',z') (build_grid (x,y,z) (x',y',z')) in
    Warp_size <> 0 -> forall i,
      i >= x*y*z*(next_multiple (x'*y'*z') Warp_size) ->
    count i (physical_thread_set (warps g (get_physical_id (x,y,z) (x',y',z'))) f) 0.
Proof.
  intros.
  simpl in *. clear g.
  set (g := fun (i j k i' j' k' : nat) => (i,j,k,(i',j',k'))).
  assert (forall idx idy idz, idx < x -> idy < y -> idz < z -> count i (physical_thread_set (warps (block (x',y',z') (idx,idy,idz) (g idx idy idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0).
    intros. apply warp_end_block. apply H. simpl. repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.mul_1_r).
    repeat (rewrite Nat.add_0_r).
    assert (idx * next_multiple (x' * y' * z') Warp_size <= next_multiple (x' * y' * z') Warp_size * (Nat.pred x)).
        rewrite Nat.mul_comm.
        apply Nat.mul_le_mono_l.
        apply Nat.lt_le_pred. apply H1.
    assert (idy * next_multiple (x' * y' * z') Warp_size <= next_multiple (x' * y' * z') Warp_size * Nat.pred y).
        rewrite Nat.mul_comm.
        apply Nat.mul_le_mono_l.
        apply Nat.lt_le_pred. apply H2.
    assert (idz * next_multiple (x' * y' * z') Warp_size <= next_multiple (x' * y' * z') Warp_size * Nat.pred z).
        rewrite Nat.mul_comm.
        apply Nat.mul_le_mono_l.
        apply Nat.lt_le_pred. apply H3.
    apply Nat.le_trans with (m := x*y*z*next_multiple (x' * (y' * z')) Warp_size).
      apply Nat.le_trans with (m := next_multiple (x' * y' * z') Warp_size * Nat.pred x +
        x * next_multiple (x' * y' * z') Warp_size * Nat.pred y +
        x * y * next_multiple (x' * y' * z') Warp_size * Nat.pred z +
        next_multiple (x' * (y' * z')) Warp_size).
        repeat (rewrite <- Nat.add_assoc). apply Nat.add_le_mono.
        apply H4.
        apply Nat.add_le_mono.
        assert (idy * x * next_multiple (x' * y' * z') Warp_size = x * idy * next_multiple (x' * y' * z') Warp_size).
        rewrite Nat.mul_comm. rewrite Nat.mul_assoc.
        rewrite Nat.mul_comm.
        rewrite Nat.mul_comm with (m := idy). rewrite Nat.mul_assoc. reflexivity.
        rewrite H7. repeat (rewrite <- Nat.mul_assoc). apply Nat.mul_le_mono_l.
        repeat (rewrite Nat.mul_assoc). apply H5.
        assert (idz * x * y = x * y * idz).
        rewrite Nat.mul_comm. rewrite Nat.mul_assoc.
        rewrite Nat.mul_comm. rewrite Nat.mul_assoc. reflexivity.
        rewrite H7.
        repeat (rewrite <- Nat.mul_assoc). apply Nat.add_le_mono_r.
        apply Nat.mul_le_mono_l. apply Nat.mul_le_mono_l. repeat (rewrite Nat.mul_assoc). apply H6.
        clear H4. clear H5. clear H6.
        rewrite Nat.add_comm. repeat (rewrite Nat.add_assoc).
        repeat (rewrite Nat.mul_assoc).
        assert (next_multiple (x' * y' * z') Warp_size +
          next_multiple (x' * y' * z') Warp_size * Nat.pred x
          = next_multiple (x' * y' * z') Warp_size * x).
        rewrite Nat.mul_pred_r.
        rewrite Nat.add_sub_assoc. rewrite Nat.add_comm.
        rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
        rewrite Nat.add_0_r. reflexivity. apply le_n.
        assert (next_multiple (x' * y' * z') Warp_size * 1 <= next_multiple (x' * y' * z') Warp_size * x).
        apply Nat.mul_le_mono_l. destruct x. inversion H1. apply Nat.lt_0_succ.
        rewrite Nat.mul_1_r in H4. apply H4. rewrite H4. clear H4.
        assert (next_multiple (x' * y' * z') Warp_size * x +
            x * next_multiple (x' * y' * z') Warp_size * Nat.pred y
            = x * next_multiple (x' * y' * z') Warp_size * y).
          rewrite Nat.mul_comm.
          rewrite Nat.mul_pred_r.
          rewrite Nat.add_sub_assoc. rewrite Nat.add_comm.
          rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
          rewrite Nat.add_0_r. reflexivity. apply le_n.
          assert (x * next_multiple (x' * y' * z') Warp_size * 1 <= x * next_multiple (x' * y' * z') Warp_size * y).
          apply Nat.mul_le_mono_l. destruct y. inversion H2. apply Nat.lt_0_succ.
          rewrite Nat.mul_1_r in H4. apply H4. rewrite H4. clear H4.
        assert (x * next_multiple (x' * y' * z') Warp_size * y +
              x * y * next_multiple (x' * y' * z') Warp_size * Nat.pred z =
              x * y * next_multiple (x' * y' * z') Warp_size * z).
          assert (x * next_multiple (x' * y' * z') Warp_size * y =
                  x * y * next_multiple (x' * y' * z') Warp_size).
             rewrite Nat.mul_comm. rewrite Nat.mul_assoc. rewrite Nat.mul_comm with (n := y). reflexivity.
            rewrite H4; clear H4.
          rewrite Nat.mul_pred_r.
          rewrite Nat.add_sub_assoc. rewrite Nat.add_comm.
          rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
          rewrite Nat.add_0_r. reflexivity. apply le_n.
          assert (x * y * next_multiple (x' * y' * z') Warp_size * 1 <= x * y * next_multiple (x' * y' * z') Warp_size * z).
          apply Nat.mul_le_mono_l. destruct z. inversion H3. apply Nat.lt_0_succ.
          rewrite Nat.mul_1_r in H4. apply H4. rewrite H4. clear H4.
          assert (x * y * next_multiple (x' * y' * z') Warp_size * z
              = x * y * z * next_multiple (x' * y' * z') Warp_size).
            rewrite <- Nat.mul_assoc. rewrite Nat.mul_comm with (m := z).
            rewrite Nat.mul_assoc. reflexivity. rewrite H4. apply le_n.
      repeat (rewrite Nat.mul_assoc). apply H0.
      simpl in H1.
      assert (forall T n (f : nat -> List T) i, (forall j, j < n -> count i (f j) 0) -> count i (zip (buildList n f)) 0). {
        clear.
        induction n.
        - intros. apply empty.
        - intros. simpl. apply cat_count with (n := 0) (m := 0).
          apply H. apply le_n. apply IHn. intros. apply le_S in H0. apply H in H0.
          apply H0.
      }
      apply H2. intros idx Hx.
      apply H2. intros idy Hy.
      apply H2. intros idz Hz.
      apply H1; assumption.
Qed.

Proposition warp_contiguous_grid :
  forall x' y' z' x y z f,
  let g := grid (x,y,z) (x',y',z') (build_grid (x,y,z) (x',y',z')) in
    Warp_size <> 0 -> forall i,
      i < x*y*z*(next_multiple (x'*y'*z') Warp_size) ->
    count i (physical_thread_set (warps g (get_physical_id (x,y,z) (x',y',z'))) f) 1.
Proof.
  intros.
  simpl. clear g.
  set (g := fun (i j k i' j' k' : nat) => (i,j,k,(i',j',k'))).
  set (idx := (i/(next_multiple (x'*y'*z') Warp_size)) mod x).
  set (idy := (i/(next_multiple (x'*y'*z') Warp_size)/x) mod y).
  set (idz := (i/(next_multiple (x'*y'*z') Warp_size)/x/y)).
  assert (idx * next_multiple (x' * y' * z') Warp_size +
      idy * x * next_multiple (x' * y' * z') Warp_size +
      idz * x * y * next_multiple (x' * y' * z') Warp_size =
      i / next_multiple (x' * y' * z') Warp_size * next_multiple (x' * y' * z') Warp_size). {
          repeat (rewrite <- Nat.mul_add_distr_r).
          assert ((idx + idy * x + idz * x * y) = i / next_multiple (x' * y' * z') Warp_size). {
            unfold idx,idy,idz. clear idx. clear idy. clear idz.
            set (a := i / next_multiple (x' * y' * z') Warp_size) in *.
            rewrite Nat.div_mod_eq with (x := a) (y := x).
            assert ((x * (a / x) + a mod x) mod x = a mod x).
              rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add.
              apply Nat.Div0.mod_mod.
            rewrite H1. clear H1.
            assert (((x * (a / x) + a mod x) / x) mod y = (a / x) mod y).
              rewrite Nat.mul_comm. rewrite Nat.div_add_l.
              assert (a mod x / x = 0). apply Nat.div_small_iff.
              intro. subst. simpl in H0. inversion H0.
              apply Nat.mod_upper_bound. intro; subst; inversion H0.
              rewrite H1. rewrite Nat.add_0_r. reflexivity.
              intro; subst; inversion H0.
              rewrite H1. clear H1.
              rewrite Nat.div_mod_eq with (x := a/x) (y := y).
              assert ((y * (a / x / y) + (a / x) mod y) mod y * x =
                    x * ((a / x) mod y)).
                  rewrite Nat.mul_comm with (m := x).
                  rewrite Nat.add_comm. rewrite Nat.mul_comm with (n := y). rewrite Nat.Div0.mod_add.
                  rewrite Nat.Div0.mod_mod. reflexivity.
              rewrite H1. clear H1.
              assert ((x * (y * (a / x / y) + (a / x) mod y) + a mod x) / x / y * x * y =
                x * y * (a / x / y)).
                  rewrite Nat.mul_comm with (n := x). rewrite Nat.div_add_l.
                  assert (a mod x / x = 0). apply Nat.div_small_iff.
                    intro; subst; inversion H0.
                    apply Nat.mod_upper_bound. intro; subst; inversion H0.
                    rewrite H1. clear H1. rewrite Nat.add_0_r.
                  rewrite Nat.mul_comm with (n := y). rewrite Nat.div_add_l.
                  assert ((a/x) mod y / y = 0). apply Nat.div_small_iff.
                  intro; subst; rewrite Nat.mul_0_r in H0; inversion H0.
                  apply Nat.mod_upper_bound. intro; subst; rewrite Nat.mul_0_r in H0; inversion H0.
                  rewrite H1. rewrite Nat.add_0_r. clear H1.
                  rewrite Nat.mul_comm with (m := x). rewrite Nat.mul_comm with (m := y).
                  rewrite Nat.mul_assoc. rewrite Nat.mul_comm with (n := y). reflexivity.
                  intro; subst; rewrite Nat.mul_0_r in H0; inversion H0.
                  intro; subst; inversion H0. rewrite H1. clear H1.
                  rewrite Nat.add_comm with (m := a mod x).
                  rewrite Nat.add_comm with (m := (a/x) mod y).
                  rewrite Nat.mul_add_distr_l. rewrite Nat.add_assoc. rewrite Nat.mul_assoc. reflexivity.
          } rewrite H1. reflexivity.
      }
  assert (count i (physical_thread_set (warps (block (x',y',z') (idx,idy,idz) (g idx idy idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 1).
      apply warp_contiguous_block.
      apply H.
      simpl. repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
      rewrite H1. rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
      simpl. repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
      repeat (rewrite Nat.mul_1_r).
      rewrite H1. set (b := next_multiple (x' * y' * z') Warp_size) in *.
      assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
        apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H2 in H0.
        rewrite Nat.mul_0_r in H0. inversion H0.
      rewrite <- Nat.div_mod with (x := i) (y := b) in H2. apply H2.
      intro. rewrite H3 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
      assert (forall T i0 x y z (f : nat -> nat -> nat -> List T) X Y Z, X < x -> Y < y -> Z < z -> count i0 (f X Y Z) 1 ->
              (forall i j k, i < x -> j < y -> k < z -> (i,j,k) = (X,Y,Z) \/ count i0 (f i j k) 0) ->
              count i0 (zip (buildList x (fun i => zip (buildList y (fun j => (zip (buildList z (fun k => f i j k)))))))) 1). {
          clear.
          assert (Hz:forall T i0 z (f : nat -> List T) Z, Z < z -> count i0 (f Z) 1 ->
                      (forall k, k < z -> k = Z \/ count i0 (f k) 0) ->
                      count i0 (zip (buildList z (fun k => f k))) 1). {
                  induction z.
                  - intros. inversion H.
                  - intros. simpl. inversion H; subst.
                      + apply cat_count with (n := 0) (m := 1). apply H0.
                      assert (forall k, k < z -> count i0 (f k) 0). intros. apply le_S in H2 as H2'. apply H1 in H2'.
                      destruct H2'. subst. apply Nat.lt_irrefl in H2. exfalso. apply H2. apply H3.
                      clear IHz. clear H1. clear H. clear H0. induction z. apply empty. simpl.
                      apply cat_count with (n := 0) (m := 0). apply H2. apply le_n. apply IHz. intros. apply le_S in H. apply H2. apply H.
                      + apply cat_count with (n := 1) (m := 0).
                      assert (z < S z). apply le_n. apply H1 in H2. destruct H2. subst.
                      apply Nat.lt_irrefl in H3. exfalso. apply H3. apply H2.
                      apply IHz with (Z := Z). apply H3. apply H0. intros. apply H1. apply le_S. apply H2.
              }
          assert (Hy:forall T i0 y z (f : nat -> nat -> List T) Y Z, Y < y -> Z < z -> count i0 (f Y Z) 1 ->
                  (forall j k, j < y -> k < z -> (j,k) = (Y,Z) \/ count i0 (f j k) 0) ->
                  count i0 (zip (buildList y (fun j => (zip (buildList z (fun k => f j k)))))) 1). {
              induction y.
              - intros. inversion H.
              - intros. simpl. inversion H; subst.
                  + apply cat_count with (n := 0) (m := 1). apply Hz with (Z := Z).
                  apply H0. apply H1. intros. apply H2 with (k := k) in H. destruct H.
                  left. inversion H. reflexivity. right. apply H. apply H3.
                  assert (forall j k, j < y -> k < z -> count i0 (f j k) 0).
                    intros. apply le_S in H3 as H3'. apply H2 with (k := k) in H3'.
                    destruct H3'. inversion H5. subst. apply Nat.lt_irrefl in H3. exfalso. apply H3.
                    apply H5. apply H4.
                    clear IHy. clear Hz. clear H1. clear H. clear H0. clear H2. induction y.
                    apply empty. simpl. apply cat_count with (n := 0) (m := 0). clear IHy.
                    induction z. apply empty. simpl. apply cat_count with (n := 0) (m := 0).
                    apply H3. apply le_n. apply le_n. apply IHz. intros. apply le_S in H0.
                    apply H3. apply H. apply H0. apply IHy. intros. apply le_S in H.
                    apply H3. apply H. apply H0.
                  + apply cat_count with (n := 1) (m := 0).
                  assert (y < S y). apply le_n. destruct z. inversion H0.
                  apply H2 with (k := z) in H3. destruct H3. inversion H3. subst.
                  apply Nat.lt_irrefl in H4. exfalso. apply H4. simpl.
                  apply cat_count with (n := 0) (m := 0). apply H3.
                  clear H. clear H3. clear H1. clear H0. clear IHy. clear Hz.
                  induction z. apply empty. simpl. apply cat_count with (n := 0) (m := 0).
                  assert ((y, z) = (Y, Z) \/ count i0 (f y z) 0). apply H2. apply le_n. apply le_S. apply le_n.
                  destruct H. inversion H. subst. apply Nat.lt_irrefl in H4. exfalso. apply H4.
                  apply H. apply IHz. intros. apply H2. apply H. apply le_S in H0. apply H0.
                  apply le_n.
                  apply IHy with (Y := Y) (Z := Z). apply H4. apply H0. apply H1. intros. apply H2. apply le_S. apply H3. apply H5.
          }
          induction x.
          - intros. inversion H.
          - intros. simpl. inversion H; subst.
              + apply cat_count with (n := 0) (m := 1). apply Hy with (Y := Y) (Z := Z).
                  apply H0. apply H1. apply H2. intros. apply H3 with (k := k) (j := j) in H. destruct H.
                  left. inversion H. reflexivity. right. apply H. apply H4. apply H5.
                  assert (forall i j k, i < x -> j < y -> k < z -> count i0 (f i j k) 0).
                    intros. apply le_S in H4 as H4'. apply H3 with (k := k) (j := j) in H4'.
                    destruct H4'. inversion H7. subst. apply Nat.lt_irrefl in H4. exfalso. apply H4.
                    apply H7. apply H5. apply H6.
                    clear IHx. clear Hz. clear Hy. clear H1. clear H. clear H0. clear H2. clear H3. induction x.
                    apply empty. simpl. apply cat_count with (n := 0) (m := 0). clear IHx.
                    induction y. apply empty. simpl. apply cat_count with (n := 0) (m := 0). clear IHy.
                    induction z. apply empty. simpl. apply cat_count with (n := 0) (m := 0).
                    apply H4. apply le_n. apply le_n. apply le_n. apply IHz. intros. apply le_S in H1.
                    apply H4. apply H. apply H0. apply H1.
                    apply IHy. intros. apply H4.
                    apply H. apply le_S. apply H0. apply H1.
                    apply IHx. intros. apply le_S in H.
                    apply H4. apply H. apply H0. apply H1.
                  + apply cat_count with (n := 1) (m := 0).
                  assert (x < S x). apply le_n. destruct z. inversion H1. destruct y. inversion H0.
                  apply H3 with (k := z) (j := y) in H4. destruct H4. inversion H4. subst.
                  apply Nat.lt_irrefl in H5. exfalso. apply H5. simpl.
                  apply cat_count with (n := 0) (m := 0). apply cat_count with (n := 0) (m := 0). apply H4.
                  clear H. clear H4. clear H1. clear H0. clear H2. clear IHx. clear Hz. clear Hy.
                  induction z. apply empty. simpl. apply cat_count with (n := 0) (m := 0).
                  assert ((x,y, z) = (X,Y, Z) \/ count i0 (f x y z) 0). apply H3. apply le_n. apply le_n. apply le_S. apply le_n.
                  destruct H. inversion H. subst. apply Nat.lt_irrefl in H5. exfalso. apply H5.
                  apply H. apply IHz. intros. apply H3. apply H. apply H0. apply le_S in H1. apply H1.
                  clear H. clear H4. clear H1. clear H0. clear H2. clear IHx. clear Hz. clear Hy.
                  induction y. apply empty.  simpl. apply cat_count with (n := 0) (m := 0).
                  assert ((x,y, z) = (X,Y, Z) \/ count i0 (f x y z) 0). apply H3. apply le_n. apply le_S. apply le_n. apply le_n.
                  destruct H. inversion H. subst. apply Nat.lt_irrefl in H5. exfalso. apply H5. apply cat_count with (n := 0) (m := 0).
                  apply H. clear H. clear IHy.
                      induction z. apply empty. simpl. apply cat_count with (n := 0) (m := 0).
                      assert ((x,y, z) = (X,Y, Z) \/ count i0 (f x y z) 0). apply H3. apply le_n. apply le_S. apply le_n. apply le_S. apply le_n.
                      destruct H. inversion H. subst. apply Nat.lt_irrefl in H5. exfalso. apply H5.
                      apply H. apply IHz. intros. apply H3. apply H. apply H0. apply le_S in H1. apply H1.
                      apply IHy. intros. apply H3. apply H. apply le_S. apply H0. apply H1.
                  apply le_n. apply le_n.
                  apply IHx with (X := X) (Y := Y) (Z := Z). apply H5. apply H0. apply H1. apply H2. intros. apply H3. apply le_S. apply H4. apply H6. apply H7.
      } apply H3 with (X := idx) (Y := idy) (Z := idz).
        unfold idx. apply Nat.mod_upper_bound. intro. subst. inversion H0.
        unfold idy. apply Nat.mod_upper_bound. intro. subst. rewrite Nat.mul_0_r in H0. inversion H0.
        unfold idz. set (b := next_multiple (x' * y' * z') Warp_size) in *.
          rewrite Nat.Div0.div_div. rewrite Nat.Div0.div_div. rewrite Nat.mul_assoc.
          clear H1. clear H2. clear H3. clear idx. clear idy. clear idz. clear g. clear H.
          rewrite Nat.mul_comm in H0. rewrite Nat.mul_assoc in H0. apply Nat.Div0.div_lt_upper_bound in H0.
          repeat (rewrite Nat.mul_assoc in H0). apply H0.
        apply H2. clear H2. clear H3.
          intros.
          assert (Hx : i0 = idx \/ i0 <> idx). apply excluded_middle.
          assert (Hy : j = idy \/ j <> idy). apply excluded_middle.
          assert (Hz : k = idz \/ k <> idz). apply excluded_middle.
          destruct Hx as [Hx | Hx],Hy as [Hy | Hy],Hz as [Hz | Hz]; subst.
            (* i = idx ; j = idy ; k = idz *)
            + left. reflexivity.
            (* i = idx ; j = idy ; k <> idz *)
            + right. assert (k > idz \/ k <= idz). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (idx,idy,k) (g idx idy k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, k = idz + S x). exists (Nat.pred (k - idz)).
                      destruct (k-idz) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= S x0 * x * y * b).
                    apply Nat.mul_le_mono_r. destruct x.
                    inversion H0. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    simpl. apply Nat.lt_0_succ. simpl in H8. rewrite Nat.add_0_r in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hz. reflexivity. assert (k < idz). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (idx,idy,k) (g idx idy k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (k = idz - S (Nat.pred (idz - k))).
                      destruct (idz- k) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite Nat.add_sub_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc. rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= S (Nat.pred (idz - k)) * x * y * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2. destruct y. inversion H3.
                    simpl. apply Nat.lt_0_succ. simpl in H6. rewrite Nat.add_0_r in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idz. inversion H8.
                    destruct (S idz - k) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
            (* i = idx ; j <> idy ; k = idz *)
            + right.
              assert (j > idy \/ j <= idy). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (idx,j,idz) (g idx j idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, j = idy + S x). exists (Nat.pred (j - idy)).
                      destruct (j-idy) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := S x0 * x * next_multiple (x' * y' * z') Warp_size).
                  rewrite Nat.add_assoc. rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= S x0 * x * b).
                    apply Nat.mul_le_mono_r. destruct x.
                    inversion H0. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    simpl. apply Nat.lt_0_succ. simpl in H8. rewrite Nat.add_0_r in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hy. reflexivity. assert (j < idy). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (idx,j,idz) (g idx j idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (j = idy - S (Nat.pred (idy - j))).
                      destruct (idy - j) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := b + idz * x * y * b). rewrite Nat.add_assoc. rewrite Nat.add_sub_assoc.
                  assert (b + idz * x * y * b + idx * b + idy * x * b = idx * b + idy * x * b + idz * x * y * b + b).
                    rewrite <- Nat.add_assoc. rewrite Nat.add_comm. rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc. reflexivity. rewrite H6. clear H6. rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= S (Nat.pred (idy - j)) * x * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2.
                    simpl. apply Nat.lt_0_succ. simpl in H6. rewrite Nat.add_0_r in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idy. inversion H8.
                    destruct (S idy - j) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
            (* i = idx ; j <> idy ; k <> idz *)
            + right. assert (k > idz \/ k <= idz). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (idx,j,k) (g idx j k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, k = idz + S x). exists (Nat.pred (k - idz)).
                      destruct (k-idz) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). apply Nat.lt_le_trans with (m :=
                      idx * next_multiple (x' * y' * z') Warp_size +
                      idy * x * next_multiple (x' * y' * z') Warp_size +
                      idz * x * y * next_multiple (x' * y' * z') Warp_size +
                      (S x0 * y - idy + j) * x * next_multiple (x' * y' * z') Warp_size). rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= (S x0 * y - idy + j) * x * b).
                    apply Nat.mul_le_mono_r. destruct x.
                    inversion H0. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    assert (S x0 * S y - idy + j > 0).
                      assert (idy < S y). apply Nat.mod_upper_bound. intro. inversion H8.
                      assert (S x0 * S y - idy > 0).
                        rewrite Nat.mul_succ_l. rewrite <- Nat.add_sub_assoc.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_le_lt_mono.
                        apply le_0_n. apply Nat.sub_gt in H8. destruct (S y - idy) eqn:E.
                        exfalso. apply H8. reflexivity. apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H8.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_lt_le_mono. apply H9.
                        apply le_0_n. destruct (S x0 * S y - idy + j) eqn : E. inversion H8. simpl.
                        apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
                    rewrite <- Nat.mul_assoc with (n := (S x0 * y - idy + j)).
                    rewrite Nat.mul_add_distr_r. rewrite Nat.mul_sub_distr_r.
                    rewrite Nat.add_assoc. rewrite Nat.add_comm with (m := j * (x * next_multiple (x' * y' * z') Warp_size)).
                    repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm with (n := j * (x * next_multiple (x' * y' * z') Warp_size)).
                    rewrite <- Nat.add_assoc with (m := idy * x * next_multiple (x' * y' * z') Warp_size).
                    rewrite Nat.add_comm with (n:= idy * x * next_multiple (x' * y' * z') Warp_size).
                    rewrite Nat.add_assoc. rewrite Nat.add_sub_assoc. repeat (rewrite <- Nat.add_assoc).
                    rewrite Nat.add_comm with (n := idy * x * next_multiple (x' * y' * z') Warp_size).
                    repeat (rewrite Nat.add_assoc). rewrite <- Nat.add_sub_assoc.
                    repeat (rewrite Nat.mul_assoc). rewrite Nat.sub_diag. rewrite Nat.add_0_r.
                    assert (S x0 * y * x = S x0 * x * y). rewrite <- Nat.mul_assoc. rewrite Nat.mul_comm with (n := y).
                    rewrite Nat.mul_assoc. reflexivity. rewrite H7. apply le_n.
                    repeat (rewrite Nat.mul_assoc). apply le_n.
                    apply Nat.mul_le_mono_r. assert (idy < y). apply Nat.mod_upper_bound.
                    intro. subst. rewrite Nat.mul_0_r in H0. inversion H0. simpl.
                    rewrite <- Nat.add_0_r with (n := idy). apply Nat.add_le_mono. apply Nat.lt_le_incl.
                    apply H7. apply le_0_n.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hz. reflexivity. assert (k < idz). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (idx,j,k) (g idx j k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (k = idz - S (Nat.pred (idz - k))).
                      destruct (idz- k) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite Nat.add_sub_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc.
                  apply Nat.le_trans with (m := idx * b + idy * x * b + idz * x * y * b + b - (S (Nat.pred (idz - k)) * y - j + idy) * x * b).
                  rewrite <- Nat.mul_assoc with (n := (S (Nat.pred (idz - k)) * y - j + idy)).
                  rewrite Nat.mul_add_distr_r.
                  rewrite Nat.mul_sub_distr_r.
                  apply Nat.le_sub_le_add_r. rewrite <- Nat.add_sub_swap.
                  rewrite Nat.sub_add_distr. 
                  apply Nat.le_add_le_sub_r with (p := idy * (x * b)).
                  apply Nat.le_add_le_sub_r.
                  rewrite Nat.add_sub_assoc with (p := j * (x * b)).
                  apply Nat.le_sub_le_add_r.
                  rewrite Nat.add_comm with (m := j * (x * b)).
                  rewrite Nat.add_comm with (m := j * x * b).
                  rewrite Nat.add_comm with (m := idy * x * b).
                  do 3 (
                  rewrite <- Nat.add_assoc with (p := idy * (x * b));
                  rewrite Nat.add_comm with (m := idy * (x * b));
                  rewrite Nat.add_assoc).
                  repeat (rewrite Nat.add_assoc). repeat (rewrite Nat.mul_assoc).
                  rewrite <- Nat.mul_assoc with (m := y) (p := x). rewrite Nat.mul_comm with (n := y).
                  rewrite Nat.mul_assoc. apply le_n.
                  apply Nat.mul_le_mono_r. rewrite <- Nat.mul_1_l with (n := j).
                  apply Nat.mul_le_mono. apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H3.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (
                    rewrite <- Nat.add_assoc with (m := idy * x * b);
                    rewrite Nat.add_comm with (n := idy * x * b);
                  rewrite Nat.add_assoc). apply Nat.add_le_mono_r.
                  apply Nat.le_trans with (m := idz * x * y * b).
                  apply Nat.le_trans with (m := idz * x * y * b - j * x * b).
                  apply Nat.sub_le_mono_r. rewrite <- Nat.mul_assoc with (m := y).
                  rewrite Nat.mul_comm with (n := y). rewrite Nat.mul_assoc.
                  repeat (apply Nat.mul_le_mono_r).
                  destruct (idz - k) eqn : E. destruct idz. inversion H8.
                  apply Nat.lt_0_succ. simpl in *. rewrite <- E. apply Nat.le_sub_l.
                  apply Nat.le_sub_l. rewrite Nat.add_comm with (m := idz * x * y * b).
                  rewrite <- Nat.add_assoc.
                  apply Nat.le_add_r. rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= (S (Nat.pred (idz - k)) * y - j + idy) * x * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2.
                    destruct y. inversion H3.
                    assert (S (Nat.pred (idz - k)) * S y > j).
                       rewrite Nat.mul_succ_l.
                        rewrite <- Nat.add_0_l. apply Nat.add_le_lt_mono. apply le_0_n.
                        apply H3.
                    apply Nat.sub_gt in H6.
                    destruct (S (Nat.pred (idz - k)) * S y - j) eqn : E. exfalso. apply H6. reflexivity.
                    simpl. apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idz. inversion H8.
                    destruct (S idz - k) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
            (* i <> idx ; j = idy ; k = idz *)
            + right.
              assert (i0 > idx \/ i0 <= idx). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (i0,idy,idz) (g i0 idy idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, i0 = idx + S x). exists (Nat.pred (i0 - idx)).
                      destruct (i0-idx) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). rewrite <- Nat.add_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := S x0 * next_multiple (x' * y' * z') Warp_size).
                  repeat (rewrite Nat.add_assoc). rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= S x0 * b).
                    apply Nat.mul_le_mono_r.
                    simpl. apply Nat.lt_0_succ. simpl in H8. rewrite Nat.add_0_r in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hx. reflexivity. assert (i0 < idx). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (i0,idy,idz) (g i0 idy idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (i0 = idx - S (Nat.pred (idx - i0))).
                      destruct (idx - i0) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite <- Nat.add_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := idx * b - S (Nat.pred (idx - i0)) * b). repeat (rewrite Nat.add_assoc). rewrite Nat.add_sub_assoc.
                  assert (idy * x * b + b + idz * x * y * b + idx * b = idx * b + idy * x * b + idz * x * y * b + b).
                    rewrite Nat.add_comm. rewrite <- Nat.add_assoc.  rewrite Nat.add_comm with (n := b). repeat (rewrite Nat.add_assoc). reflexivity. rewrite H6. clear H6. rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= S (Nat.pred (idx - i0)) * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2.
                    simpl. apply Nat.lt_0_succ. simpl in H6. rewrite Nat.add_0_r in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idx. inversion H8.
                    destruct (S idx - i0) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
            (* i <> idx ; j = idy ; k <> idz *)
            + right. assert (k > idz \/ k <= idz). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (i0,idy,k) (g i0 idy k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, k = idz + S x). exists (Nat.pred (k - idz)).
                      destruct (k-idz) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). apply Nat.lt_le_trans with (m :=
                      idx * next_multiple (x' * y' * z') Warp_size +
                      idy * x * next_multiple (x' * y' * z') Warp_size +
                      idz * x * y * next_multiple (x' * y' * z') Warp_size +
                      (S x0  * x * y - idx + i0) * next_multiple (x' * y' * z') Warp_size). rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= (S x0  * x * y - idx + i0) * b).
                    apply Nat.mul_le_mono_r. destruct x.
                    inversion H0. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    assert (S x0 * S x * S y - idx + i0 > 0).
                      assert (idx < S x). apply Nat.mod_upper_bound. intro. inversion H8.
                      assert (S x0 * S x * S y - idx > 0).
                        rewrite Nat.mul_succ_l. rewrite Nat.mul_add_distr_r. rewrite <- Nat.add_sub_assoc.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_le_lt_mono.
                        apply le_0_n. rewrite Nat.mul_succ_r. rewrite <- Nat.add_0_r with (n := 0).
                        rewrite <- Nat.add_sub_assoc. apply Nat.add_le_lt_mono. apply le_0_n. apply Nat.sub_gt in H8. destruct (S x - idx) eqn:E.
                        exfalso. apply H8. reflexivity. apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H8.
                        rewrite <- Nat.mul_1_r with (n := idx). apply Nat.mul_le_mono. apply Nat.lt_le_incl. apply H8.
                        apply Nat.lt_0_succ.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_lt_le_mono. apply H9.
                        apply le_0_n. destruct (S x0 * S x * S y - idx + i0) eqn : E. inversion H8. simpl.
                        apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
                    rewrite Nat.mul_add_distr_r. rewrite Nat.mul_sub_distr_r.
                    rewrite Nat.add_assoc. rewrite Nat.add_comm.
                    repeat (rewrite <- Nat.add_assoc). rewrite Nat.add_comm with (n := idx * next_multiple (x' * y' * z') Warp_size).
                    repeat (rewrite Nat.add_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := idx * next_multiple (x' * y' * z') Warp_size).
                    rewrite Nat.add_sub_assoc. rewrite Nat.add_comm with (n := idx * next_multiple (x' * y' * z') Warp_size). repeat (rewrite <- Nat.add_assoc).
                    rewrite <- Nat.add_sub_assoc.
                    repeat (rewrite Nat.mul_assoc). rewrite Nat.sub_diag. rewrite Nat.add_0_r.
                    apply le_n. apply le_n.
                    apply Nat.mul_le_mono_r. assert (idx < x). apply Nat.mod_upper_bound.
                    intro. subst. inversion H0. rewrite <- Nat.mul_1_r with (n := idx).
                    rewrite <- Nat.mul_1_l with (n := idx). apply Nat.mul_le_mono. apply Nat.mul_le_mono.
                    apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H7. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    apply Nat.lt_0_succ.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hz. reflexivity. assert (k < idz). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (i0,idy,k) (g i0 idy k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (k = idz - S (Nat.pred (idz - k))).
                      destruct (idz- k) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite Nat.add_sub_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc.
                  apply Nat.le_trans with (m := idx * b + idy * x * b + idz * x * y * b + b - (S (Nat.pred (idz - k)) * x * y - i0 + idx) * b).
                  rewrite Nat.mul_add_distr_r.
                  rewrite Nat.mul_sub_distr_r.
                  apply Nat.le_sub_le_add_r. rewrite <- Nat.add_sub_swap.
                  rewrite Nat.sub_add_distr. 
                  apply Nat.le_add_le_sub_r.
                  apply Nat.le_add_le_sub_r.
                  rewrite Nat.add_sub_assoc.
                  apply Nat.le_sub_le_add_r.
                  rewrite Nat.add_comm with (m := i0 * b).
                  repeat (rewrite <- Nat.add_assoc). rewrite Nat.add_comm with (n := idx * b).
                  repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm with (m := idx * b).
                  repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm with (n := idx * b). apply le_n.
                  apply Nat.mul_le_mono_r. rewrite <- Nat.mul_1_r with (n := i0).
                  apply Nat.mul_le_mono. rewrite <- Nat.mul_1_l with (n := i0).
                  apply Nat.mul_le_mono. apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H2.
                  destruct y. rewrite Nat.mul_0_r in H0. inversion H0. apply Nat.lt_0_succ.
                  rewrite Nat.add_comm with (m := idx*b). repeat (rewrite <- Nat.add_assoc).
                  apply Nat.add_le_mono_l.
                  apply Nat.le_trans with (m := idz * x * y * b).
                  apply Nat.le_trans with (m := idz * x * y * b - i0 * b).
                  apply Nat.sub_le_mono_r.
                  repeat (apply Nat.mul_le_mono_r).
                  destruct (idz - k) eqn : E. destruct idz. inversion H8.
                  apply Nat.lt_0_succ. simpl in *. rewrite <- E. apply Nat.le_sub_l.
                  apply Nat.le_sub_l. rewrite Nat.add_comm with (m := idz * x * y * b + b).
                  rewrite <- Nat.add_assoc.
                  apply Nat.le_add_r. rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= (S (Nat.pred (idz - k)) * x * y - i0 + idx) * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2.
                    destruct y. inversion H3.
                    assert (S (Nat.pred (idz - k)) * S x * S y > i0).
                       rewrite Nat.mul_succ_l.
                        rewrite Nat.mul_add_distr_r.
                        rewrite <- Nat.add_0_l. apply Nat.add_le_lt_mono. apply le_0_n.
                        apply Nat.lt_le_trans with (m := S x). apply H2.
                        assert (S x * 1 <= S x * S y). apply Nat.mul_le_mono. apply le_n. apply Nat.lt_0_succ.
                        rewrite Nat.mul_1_r in H6. apply H6.
                    apply Nat.sub_gt in H6.
                    destruct (S (Nat.pred (idz - k)) * S x * S y - i0) eqn : E. exfalso. apply H6. reflexivity.
                    simpl. apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idz. inversion H8.
                    destruct (S idz - k) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
            (* i <> idx ; j <> idy ; k = idz *)
            + right. assert (j > idy \/ j <= idy). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (i0,j,idz) (g i0 j idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, j = idy + S x). exists (Nat.pred (j - idy)).
                      destruct (j-idy) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). apply Nat.lt_le_trans with (m :=
                      idx * next_multiple (x' * y' * z') Warp_size +
                      idy * x * next_multiple (x' * y' * z') Warp_size +
                      idz * x * y * next_multiple (x' * y' * z') Warp_size +
                      (S x0  * x - idx + i0) * next_multiple (x' * y' * z') Warp_size). rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= (S x0  * x - idx + i0) * b).
                    apply Nat.mul_le_mono_r. destruct x.
                    inversion H0. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    assert (S x0 * S x - idx + i0 > 0).
                      assert (idx < S x). apply Nat.mod_upper_bound. intro. inversion H8.
                      assert (S x0 * S x - idx > 0).
                        rewrite Nat.mul_succ_l. rewrite <- Nat.add_sub_assoc.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_le_lt_mono.
                        apply le_0_n. apply Nat.sub_gt in H8. destruct (S x - idx) eqn:E.
                        exfalso. apply H8. reflexivity. apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H8.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_lt_le_mono. apply H9.
                        apply le_0_n. destruct (S x0 * S x - idx + i0) eqn : E. inversion H8. simpl.
                        apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
                    rewrite Nat.mul_add_distr_r. rewrite Nat.mul_sub_distr_r.
                    rewrite Nat.add_assoc. rewrite Nat.add_comm.
                    repeat (rewrite <- Nat.add_assoc). rewrite Nat.add_comm with (n := idx * next_multiple (x' * y' * z') Warp_size).
                    repeat (rewrite Nat.add_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := idx * next_multiple (x' * y' * z') Warp_size).
                    rewrite Nat.add_sub_assoc. rewrite Nat.add_comm with (n := idx * next_multiple (x' * y' * z') Warp_size). repeat (rewrite <- Nat.add_assoc).
                    rewrite <- Nat.add_sub_assoc.
                    repeat (rewrite Nat.mul_assoc). rewrite Nat.sub_diag. rewrite Nat.add_0_r.
                    rewrite Nat.add_comm with (m := idz * x * y * next_multiple (x' * y' * z') Warp_size).
                    apply le_n. apply le_n.
                    apply Nat.mul_le_mono_r. assert (idx < x). apply Nat.mod_upper_bound.
                    intro. subst. inversion H0.
                    rewrite <- Nat.mul_1_l with (n := idx). apply Nat.mul_le_mono.
                    apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H7.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hy. reflexivity. assert (j < idy). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (i0,j,idz) (g i0 j idz)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (j = idy - S (Nat.pred (idy - j))).
                      destruct (idy - j) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite Nat.add_sub_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc.
                  apply Nat.le_trans with (m := idx * b + idy * x * b + idz * x * y * b + b - (S (Nat.pred (idy - j)) * x - i0 + idx) * b).
                  rewrite Nat.mul_add_distr_r.
                  rewrite Nat.mul_sub_distr_r.
                  apply Nat.le_add_le_sub_r. rewrite Nat.add_assoc. rewrite Nat.add_comm with (m := idx*b).
                  rewrite Nat.add_sub_assoc. rewrite Nat.add_sub_assoc.
                  apply Nat.le_sub_le_add_r. rewrite <- Nat.add_sub_assoc.
                  repeat (rewrite <- Nat.add_assoc). rewrite Nat.add_comm with (m := idz * x * y * b + (b + S (Nat.pred (idy - j)) * x * b)).
                  repeat (rewrite Nat.add_assoc). rewrite Nat.add_sub_assoc.
                  apply Nat.le_sub_le_add_r.
                  rewrite Nat.add_comm. repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm with (n := idy * x * b).
                  apply Nat.add_le_mono_r. repeat (rewrite <- Nat.add_assoc). apply Nat.add_le_mono_l.
                  apply Nat.add_le_mono_l. rewrite Nat.add_assoc. rewrite Nat.add_comm with (n := i0 * b).
                  rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc.
                  apply le_n.
                  apply Nat.mul_le_mono_r.
                  apply Nat.mul_le_mono_r.
                  destruct (idy - j) eqn : E. destruct idy. inversion H8.
                  apply Nat.lt_0_succ. simpl in *. rewrite <- E. apply Nat.le_sub_l.
                  apply Nat.mul_le_mono_r.
                  apply Nat.mul_le_mono_r.
                  destruct (idy - j) eqn : E. destruct idy. inversion H8.
                  apply Nat.lt_0_succ. simpl in *. rewrite <- E. apply Nat.le_sub_l.
                  rewrite <- Nat.add_sub_assoc. repeat (rewrite <- Nat.add_assoc).
                  apply Nat.le_add_r.
                  apply Nat.mul_le_mono_r.
                  apply Nat.mul_le_mono_r.
                  destruct (idy - j) eqn : E. destruct idy. inversion H8.
                  apply Nat.lt_0_succ. simpl in *. rewrite <- E. apply Nat.le_sub_l.
                  apply Nat.mul_le_mono_r. rewrite <- Nat.mul_1_l with (n := i0).
                  apply Nat.mul_le_mono. apply Nat.lt_0_succ. apply Nat.lt_le_incl. apply H2.
                  rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= (S (Nat.pred (idy - j)) * x - i0 + idx) * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2.
                    destruct y. inversion H3.
                    assert (S (Nat.pred (idy - j)) * S x > i0).
                       rewrite Nat.mul_succ_l.
                        rewrite <- Nat.add_0_l. apply Nat.add_le_lt_mono. apply le_0_n.
                        apply H2.
                    apply Nat.sub_gt in H6.
                    destruct (S (Nat.pred (idy - j)) * S x - i0) eqn : E. exfalso. apply H6. reflexivity.
                    simpl. apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idy. inversion H8.
                    destruct (S idy - j) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
            (* i <> idx ; j <> idy ; k <> idz *)
            + right. assert (k > idz \/ k <= idz). apply Nat.lt_ge_cases. destruct H5.
              * assert (count i (physical_thread_set (warps (block (x',y',z') (i0,j,k) (g i0 j k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_start_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (exists x, k = idz + S x). exists (Nat.pred (k - idz)).
                      destruct (k-idz) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in E. apply E in H5.
                      exfalso. apply H5. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H5.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H5.
                  destruct H6. rewrite H6. repeat (rewrite <- Nat.mul_assoc). rewrite Nat.mul_add_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc). apply Nat.lt_le_trans with (m :=
                      idx * next_multiple (x' * y' * z') Warp_size +
                      idy * x * next_multiple (x' * y' * z') Warp_size +
                      idz * x * y * next_multiple (x' * y' * z') Warp_size +
                      (S x0  * x * y - idx - idy * x + i0 + j * x) * next_multiple (x' * y' * z') Warp_size). rewrite H1.
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  assert (b * (i / b) + i mod b < i / b * b + b). rewrite Nat.mul_comm.
                    apply Nat.add_lt_mono_l. apply Nat.mod_upper_bound. intro. rewrite H7 in H0.
                    rewrite Nat.mul_0_r in H0. inversion H0.
                  rewrite <- Nat.div_mod with (x := i) (y := b) in H7.
                  apply Nat.le_trans with (m := i/b*b+b). apply H7.
                  apply Nat.add_le_mono_l.
                  assert (1*b <= (S x0 * x * y - idx - idy * x + i0 + j * x) * b).
                    apply Nat.mul_le_mono_r. destruct x.
                    inversion H0. destruct y. rewrite Nat.mul_0_r in H0. inversion H0.
                    assert (S x0 * S x * S y - idx - idy * S x + i0 + j * S x > 0).
                      assert (idx < S x). apply Nat.mod_upper_bound. intro. inversion H8.
                      assert (idy < S y). apply Nat.mod_upper_bound. intro. inversion H9.
                      assert (S x0 * S x * S y - idx - idy * S x > 0).
                        rewrite Nat.mul_succ_l. rewrite Nat.mul_add_distr_r. rewrite <- Nat.add_sub_assoc. rewrite <- Nat.add_sub_assoc.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_le_lt_mono.
                        apply le_0_n. rewrite Nat.mul_succ_r.
                        rewrite <- Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite <- Nat.add_0_r with (n := 0).  apply Nat.add_lt_le_mono. apply Nat.sub_gt in H8. destruct (S x - idx) eqn:E.
                        exfalso. apply H8. reflexivity. apply Nat.lt_0_succ. apply le_0_n.
                        rewrite Nat.mul_comm. apply Nat.mul_le_mono. apply le_n. apply le_S_n. apply H9.
                        apply Nat.lt_le_incl. apply H8. rewrite Nat.mul_succ_r with (m := y). rewrite <- Nat.add_sub_assoc.
                        rewrite <- Nat.add_0_r with (n := idy * S x). apply Nat.add_le_mono.
                        rewrite Nat.mul_comm. apply Nat.mul_le_mono. apply le_n. apply le_S_n. apply H9. apply le_0_n.
                        apply Nat.lt_le_incl. apply H8.
                        rewrite <- Nat.mul_1_r with (n := idx). apply Nat.mul_le_mono. apply Nat.lt_le_incl. apply H8.
                        apply Nat.lt_0_succ.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_lt_le_mono.
                        rewrite <- Nat.add_0_r with (n := 0). apply Nat.add_lt_le_mono. apply H10.
                        apply le_0_n. destruct (S x0 * S x * S y - idx + i0) eqn : E. inversion H8. simpl.
                        apply le_0_n. apply le_0_n. apply le_0_n. apply H8. rewrite Nat.mul_1_l in H8. apply H8.
                    intro. rewrite H8 in H0. rewrite Nat.mul_0_r in H0. inversion H0.
                    repeat (rewrite Nat.mul_add_distr_r). repeat (rewrite Nat.mul_sub_distr_r).
                    rewrite Nat.add_assoc. rewrite Nat.add_comm. rewrite Nat.add_comm with (m := j * x * next_multiple (x' * y' * z') Warp_size).
                    repeat (rewrite <- Nat.add_assoc). apply Nat.add_le_mono_l. repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm.
                    repeat (rewrite <- Nat.add_assoc). apply Nat.add_le_mono_l. rewrite <- Nat.sub_add_distr.
                    repeat (rewrite Nat.add_sub_assoc).
                    repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm. rewrite Nat.add_comm with (m := idz * x * y * next_multiple (x' * y' * z') Warp_size).
                    rewrite <- Nat.add_sub_assoc. rewrite <- Nat.add_sub_assoc.
                    rewrite Nat.sub_diag. rewrite Nat.add_0_r. rewrite Nat.add_comm. apply le_n.
                    apply le_n. apply Nat.le_add_l. rewrite Nat.add_comm. apply Nat.add_le_mono_l.
                    apply Nat.le_trans with (m := x * next_multiple (x' * y' * z') Warp_size).
                    apply Nat.mul_le_mono_r. assert (idx < x). apply Nat.mod_upper_bound.
                    intro. subst. inversion H0. apply Nat.lt_le_incl. apply H7.
                    rewrite <- Nat.add_0_l with (n := x * next_multiple (x' * y' * z') Warp_size). apply Nat.add_le_mono.
                    apply le_0_n. apply Nat.mul_le_mono_r. assert (x * 1 <= S x0 * x * y).
                    apply Nat.mul_le_mono. assert (1 * x <= S x0 * x).
                    apply Nat.mul_le_mono. apply Nat.lt_0_succ. apply le_n.
                    rewrite Nat.mul_1_l in H7. apply H7. destruct y. rewrite Nat.mul_0_r in H0. inversion H0. apply Nat.lt_0_succ.
                    rewrite Nat.mul_1_r in H7. apply H7.
                    set (b := next_multiple (x' * y' * z') Warp_size) in *.
                    apply Nat.le_trans with (m := S x0 * x * y * b).
                    rewrite <- Nat.mul_add_distr_r. apply Nat.mul_le_mono_r.
                    apply Nat.le_trans with (m := x * y).
                    apply Nat.le_trans with (m := S idy * x). simpl. apply Nat.add_le_mono_r.
                    apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
                    intro. subst. inversion H0. rewrite Nat.mul_comm. apply Nat.mul_le_mono_l.
                    apply Nat.mod_upper_bound. intro. subst. rewrite Nat.mul_0_r in H0. inversion H0.
                    assert (1 * x * y <= S x0 * x * y). repeat (apply Nat.mul_le_mono_r). apply Nat.lt_0_succ.
                    rewrite Nat.mul_1_l in H7. apply H7. assert (0 + S x0 * x * y * b <= idz * x * y * b + S x0 * x * y * b). apply Nat.add_le_mono_r.
                    apply le_0_n. apply H7.
                    rewrite <- Nat.mul_add_distr_r. apply Nat.mul_le_mono_r.
                    apply Nat.le_trans with (m := x * y).
                    apply Nat.le_trans with (m := S idy * x). simpl. apply Nat.add_le_mono_r.
                    apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
                    intro. subst. inversion H0. rewrite Nat.mul_comm. apply Nat.mul_le_mono_l.
                    apply Nat.mod_upper_bound. intro. subst. rewrite Nat.mul_0_r in H0. inversion H0.
                    assert (1 * x * y <= S x0 * x * y). repeat (apply Nat.mul_le_mono_r). apply Nat.lt_0_succ.
                    rewrite Nat.mul_1_l in H7. apply H7.
              } apply H6.
              * inversion H5. subst. exfalso. apply Hz. reflexivity. assert (k < idz). rewrite <- H6 in *. apply le_n_S. apply H7. clear H6.
                clear H7. clear m. clear H5.
                assert (count i (physical_thread_set (warps (block (x',y',z') (i0,j,k) (g i0 j k)) (get_physical_id (x,y,z) (x',y',z'))) f) 0). {
                  apply warp_end_block. apply H. simpl.
                  repeat (rewrite Nat.mul_0_r). repeat (rewrite Nat.add_0_r).
                  repeat (rewrite Nat.mul_1_r).
                  assert (k = idz - S (Nat.pred (idz - k))).
                      destruct (idz- k) eqn:E.
                      apply Nat.sub_0_le in E. apply Nat.nlt_ge in H8. apply le_n_S in E. apply H8 in E.
                      exfalso. apply E. simpl. rewrite <- E.
                      apply Nat.lt_le_incl in H8. symmetry. apply Nat.add_sub_eq_r.
                      rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag.
                      rewrite Nat.add_0_r. reflexivity. apply le_n. apply H8.
                  rewrite H5. repeat (rewrite <- Nat.mul_assoc). rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (m := next_multiple (x' * (y' * z')) Warp_size).
                  rewrite Nat.mul_sub_distr_r.
                  repeat (rewrite Nat.mul_assoc).
                  repeat (rewrite Nat.add_assoc).
                  set (b := next_multiple (x' * y' * z') Warp_size) in *.
                  rewrite Nat.add_sub_assoc. rewrite <- Nat.add_assoc. rewrite Nat.add_comm with (n := b). rewrite Nat.add_assoc.
                  apply Nat.le_trans with (m := idx * b + idy * x * b + idz * x * y * b + b - (S (Nat.pred (idz - k)) * x * y - i0 - j * x + idx + idy * x) * b).
                  rewrite Nat.mul_add_distr_r. rewrite Nat.mul_add_distr_r.
                  rewrite <- Nat.sub_add_distr. rewrite Nat.mul_sub_distr_r.
                  apply Nat.le_sub_le_add_r. rewrite <- Nat.add_sub_swap.
                  apply Nat.le_add_le_sub_r.
                  rewrite Nat.add_comm with (m := idy * x * b).
                  rewrite Nat.add_comm with (m := idx * b).
                  repeat (rewrite Nat.add_assoc).
                  rewrite Nat.add_sub_assoc.
                  apply Nat.le_sub_le_add_r.
                  rewrite Nat.mul_add_distr_r.
                  rewrite Nat.add_comm with (m := (i0 * b + j * x * b)).
                  repeat (rewrite <- Nat.add_assoc). apply Nat.add_le_mono_l. apply Nat.add_le_mono_l.
                  repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm with (m := idz * x * y * b).
                  rewrite Nat.add_comm with (n := idx * b). repeat (rewrite <- Nat.add_assoc). apply Nat.add_le_mono_l.
                  repeat (rewrite Nat.add_assoc). rewrite Nat.add_comm with (m := b). rewrite Nat.add_assoc.
                  apply le_n.
                  apply Nat.mul_le_mono_r.
                  apply Nat.le_trans with (m := x * y).
                  apply Nat.le_trans with (m := S j * x).
                  simpl. apply Nat.add_le_mono_r. apply Nat.lt_le_incl. apply H2.
                  rewrite Nat.mul_comm. apply Nat.mul_le_mono_l. apply H3.
                  assert (1 * x * y <= S (Nat.pred (idz - k)) * x * y). repeat (apply Nat.mul_le_mono_r).
                  apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H6. apply H6.
                  rewrite <- Nat.add_assoc. rewrite Nat.add_comm. repeat (rewrite <- Nat.add_assoc). repeat (apply Nat.add_le_mono_l).
                  assert (S (Nat.pred (idz - k)) <= idz). apply Nat.sub_gt in H8.
                  destruct (idz - k) eqn:E. exfalso. apply H8. reflexivity. simpl. rewrite <- E.
                  apply Nat.le_sub_l.
                  apply Nat.mul_le_mono_r with (p := x) in H6.
                  apply Nat.mul_le_mono_r with (p := y) in H6.
                  apply Nat.mul_le_mono_r with (p := b) in H6.
                  apply Nat.le_trans with (m := idz * x * y * b).
                  apply Nat.le_trans with (S (Nat.pred (idz - k)) * x * y * b).
                  apply Nat.le_sub_l. apply H6. apply Nat.le_add_r.
                  rewrite H1.
                  apply Nat.le_trans with (m := i / b * b). apply Nat.le_sub_le_add_l.
                  rewrite Nat.add_comm with (m := b). apply Nat.add_le_mono_r.
                  assert (1*b <= (S (Nat.pred (idz - k)) * x * y - i0 - j * x + idx + idy * x) * b).
                    apply Nat.mul_le_mono_r. destruct x. inversion H2.
                    destruct y. inversion H3. rewrite <- Nat.sub_add_distr.
                    assert (S (Nat.pred (idz - k)) * S x * S y > i0 + j * S x).
                      apply Nat.lt_le_trans with (m := S x * S y).
                      apply Nat.lt_le_trans with (m := S j * S x).
                      rewrite Nat.mul_succ_l. rewrite Nat.add_comm.
                      apply Nat.add_lt_mono_l. apply H2. rewrite Nat.mul_comm.
                      apply Nat.mul_le_mono_l. apply H3.
                      assert (1 * S x * S y <= S (Nat.pred (idz - k)) * S x * S y).
                      repeat (apply Nat.mul_le_mono_r). apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H6.
                      apply H6.
                    apply Nat.sub_gt in H6.
                    destruct (S (Nat.pred (idz - k)) * S x * S y - (i0 + j * S x)) eqn : E. exfalso. apply H6. reflexivity.
                    simpl. apply Nat.lt_0_succ. rewrite Nat.mul_1_l in H6. apply H6.
                  rewrite Nat.mul_comm. apply Nat.Div0.mul_div_le.
                  repeat (apply Nat.mul_le_mono_r). destruct idz. inversion H8.
                    destruct (S idz - k) eqn : E. simpl. apply Nat.lt_0_succ.
                    simpl. rewrite <- E. apply Nat.le_sub_l.
              } apply H5.
Qed.















