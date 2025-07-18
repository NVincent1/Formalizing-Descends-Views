
From Views Require Import utils.
From Views Require Import Execution_resources.
From Views Require Import Execution_resources_lemmas.
From Views Require Import Execution_resources_functions_correctness_lemmas.
Require Import PeanoNat.

Fixpoint forall_no_error (e : execution_resource) (d : dimension) : Prop :=
  match e with
  | Collection n v => forall i, (forall_no_error (v i) d)
  | _ => for_all e d <> Error
end.

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
    apply collection_ok.
    intros.
    apply H with (n := n0) (m := n1).
    apply H0. apply H2. apply H1.
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

Proposition for_all_ok_physical :
  forall i e d m,
  forall_no_error e d -> count i (physical_thread_set e) m -> count i (physical_thread_set (for_all e d)) m
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
  - apply collection_ok_physical. intros. apply H with (n := n0) (m := n1) in H0.
    apply H0. apply H2. apply H1.
Qed.

Proposition select_correct :
  forall i e d m m' l r,
  count i (thread_set' e) m -> count i (thread_set' (select_range e l r d)) m' -> m' <= m
.
Proof.
  induction e;
  intros.
  - simpl in *. inversion H0. apply le_0_n.
  - simpl in *. inversion H0. apply le_0_n.
  - simpl in *. destruct d.
    + destruct (r <=? Warp_size).
      * simpl in *. clear H. induction (r - l).
        inversion H0. apply le_0_n.
        simpl in *. apply IHn in H0. apply H0.
      * simpl in *. inversion H0. apply le_0_n.
    + inversion H0. apply le_0_n.
    + inversion H0. apply le_0_n.
  - destruct shp as [p z]. destruct p as [x y]. destruct id as [p idz]. destruct p as [idx idy].
    destruct d.
      + destruct x.
        * simpl in *; destruct y,z; try (destruct y); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
        * destruct x.
          ** simpl in *; destruct y,z; try (destruct y); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
          ** simpl in *. destruct y,z.
            ++ destruct (r <=? S (S x)) eqn: E. simpl in H0.
            clear E. clear H. induction (r - l). inversion H0. apply le_0_n. apply IHn in H0. apply H0.
            inversion H0; apply le_0_n.
            ++ destruct z; destruct (r <=? S (S x)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct y; destruct (r <=? S (S x)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct y,z.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** apply leb_correct in E.
                assert (count i (zip (buildList (S (S x)) (fun i => (zip (buildList 1 (fun j => (buildList 1 (fun k => b i j k)))))))) m).
                rewrite <- block_ok_xyz. apply H. simpl in *.
                apply zip_buildlist_inclusion with (n := S (S x)) (f := fun i => b i 0 0 :: []) (m := m) in H0.
                apply H0. apply E. apply H1.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S x)) (f := ((fun i : nat =>
                    (thread_set_1z 1 1 (S (S z)) (fun x : ThreadId_t => x :: [])
                    (fun _ j k : nat => b i j k) ++ []) ++ [])))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) 0 (S z) :: b (S x) 0 z
                    :: (thread_set_1z (S (S x)) 1 z (fun x : ThreadId_t => x :: []) b ++ [])) in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev with (l1 := b x 0 (S z) :: b x 0 z
                    :: (thread_set_1z (S x) 1 z (fun x : ThreadId_t => x :: []) b ++ [])) in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count with (l1 := b (S x) 0 (S z) :: b (S x) 0 z
                    :: ((thread_set_1z 1 1 z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b (S x) j k)))).
                    rewrite block_ok_z in H0. rewrite block_ok_z. apply H0.
                    apply cat_count with (l1 := b x 0 (S z) :: b x 0 z
                    :: thread_set_1z 1 1 z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k)).
                    rewrite block_ok_z in H1. rewrite block_ok_z. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction x.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev with (l1 := b x 0 (S z) :: b x 0 z
                        :: (thread_set_1z (S x) 1 z (fun x : ThreadId_t => x :: []) b ++ [])) in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count with (l1 := b x 0 (S z) :: b x 0 z
                        :: ((thread_set_1z 1 1 z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
                        []) ++ [])).
                        repeat (rewrite cat_empty in *).
                        rewrite block_ok_z in H2. rewrite block_ok_z. apply H2.
                        apply IHx. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S x)) (f := ((fun i : nat =>
                    (thread_set_2yz 1 (S (S y)) 1 (fun x : ThreadId_t => x :: [])
                    (fun _ j k : nat => b i j k) ++ []))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) (S y) 0 :: b (S x) y 0
                    :: thread_set_2yz (S (S x)) y 1 (fun x : ThreadId_t => x :: []) b) in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev with (l1 := b x (S y) 0 :: b x y 0
                    :: thread_set_2yz (S x) y 1 (fun x : ThreadId_t => x :: []) b) in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count with (l1 := b (S x) (S y) 0 :: b (S x) y 0
                    :: thread_set_2yz 1 y 1 (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b (S x) j k)).
                    rewrite block_ok_yz in H0. rewrite block_ok_yz. apply H0.
                    apply cat_count with (l1 := b x (S y) 0 :: b x y 0
                    :: thread_set_2yz 1 y 1 (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k)).
                    rewrite block_ok_yz in H1. rewrite block_ok_yz. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction x.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev with (l1 := b x (S y) 0 :: b x y 0
                        :: thread_set_2yz (S x) y 1 (fun x : ThreadId_t => x :: []) b) in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count with (l1 := b x (S y) 0 :: b x y 0
                        :: (thread_set_2yz 1 y 1 (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
                        [])).
                        repeat (rewrite cat_empty in *).
                        rewrite block_ok_yz in H2. rewrite block_ok_yz. apply H2.
                        apply IHx. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S x)) (f := ((fun i : nat =>
                    (thread_set_2yz 1 (S (S y)) (S (S z)) (fun x : ThreadId_t => x :: [])
                    (fun _ j k : nat => b i j k) ++ []))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) (S y) (S z) :: b (S x) (S y) z
                    :: (thread_set_1z (S (S x)) (S (S y)) z (fun x : ThreadId_t => x :: []) b ++
                    b (S x) y (S z) :: b (S x) y z
                    :: thread_set_1z (S (S x)) (S y) z (fun x : ThreadId_t => x :: []) b ++
                    thread_set_2yz (S (S x)) y (S (S z)) (fun x : ThreadId_t => x :: []) b)) in H.
                    destruct H as [m1 [m2 [H0 [H1 H']]]]; subst.
                    simpl.
                    apply cat_count with (l1 := b (S x) (S y) (S z) :: b (S x) (S y) z
                    :: ((thread_set_1z 1 (S (S y)) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b (S x) j k) ++
                    b (S x) y (S z) :: b (S x) y z
                    :: thread_set_1z 1 (S y) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b (S x) j k) ++
                    thread_set_2yz 1 y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b (S x) j k)) ++ [])).
                    repeat (rewrite cat_empty). repeat (rewrite block_ok_z in *).
                    repeat (rewrite block_ok_yz in *). apply H0.
                    clear H0.
                    apply cat_count_rev with (l1 := b x (S y) (S z) :: b x (S y) z
                    :: (thread_set_1z (S x) (S (S y)) z (fun x : ThreadId_t => x :: []) b ++
                    b x y (S z) :: b x y z
                    :: thread_set_1z (S x) (S y) z (fun x : ThreadId_t => x :: []) b ++
                    thread_set_2yz (S x) y (S (S z)) (fun x : ThreadId_t => x :: []) b)) in H1.
                    destruct H1 as [m3 [m4 [H0 [H1 H']]]]; subst.
                    apply cat_count with (l1 := b x (S y) (S z) :: b x (S y) z
                    :: ((thread_set_1z 1 (S (S y)) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
                    b x y (S z) :: b x y z
                    :: thread_set_1z 1 (S y) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
                    thread_set_2yz 1 y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k)) ++ [])).
                    repeat (rewrite cat_empty). repeat (rewrite block_ok_z in *).
                    repeat (rewrite block_ok_yz in *). apply H0.
                    clear H0.
                    generalize dependent m4. induction x.
                    --- intros. apply H1.
                    --- simpl. intros.
                    apply cat_count_rev with (l1 := b x (S y) (S z) :: b x (S y) z
                    :: (thread_set_1z (S x) (S (S y)) z (fun x : ThreadId_t => x :: []) b ++
                    b x y (S z) :: b x y z
                    :: thread_set_1z (S x) (S y) z (fun x : ThreadId_t => x :: []) b ++
                    thread_set_2yz (S x) y (S (S z)) (fun x : ThreadId_t => x :: []) b))in H1.
                    destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
                    apply cat_count with (l1 := b x (S y) (S z) :: b x (S y) z
                    :: ((thread_set_1z 1 (S (S y)) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
                    b x y (S z) :: b x y z ::
                    thread_set_1z 1 (S y) z (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k) ++
                    thread_set_2yz 1 y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) (fun _ j k : nat => b x j k)) ++ [])).
                    repeat (rewrite cat_empty). repeat (rewrite block_ok_z in *).
                    repeat (rewrite block_ok_yz in *). apply H1.
                    clear H1. apply IHx. apply H2.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
      + destruct y.
        * simpl in *; destruct x,z; try (destruct x); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
        * destruct y.
          ** simpl in *; destruct x,z; try (destruct x); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
          ** simpl in *. destruct x,z.
            ++ destruct (r <=? S (S y)) eqn: E. simpl in H0.
            clear E. clear H. induction (r - l). inversion H0. apply le_0_n. apply IHn in H0. apply H0.
            inversion H0; apply le_0_n.
            ++ destruct z; destruct (r <=? S (S y)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x; destruct (r <=? S (S y)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x,z.
              -- simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** apply leb_correct in E.
                repeat (rewrite cat_empty in *).
                assert (count i (zip (buildList (S (S y)) (fun j => (buildList 1 (fun k => b 0 j k))))) m).
                rewrite <- block_ok_yz. apply H. simpl in *.
                apply zip_buildlist_inclusion with (n := S (S y)) (f := fun i => b 0 i 0 :: []) (m := m) in H0.
                apply H0. apply E. apply H1.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S y)) (f := ((fun j : nat =>
                    (thread_set_1z 1 1 (S (S z)) (fun x : ThreadId_t => x :: [])
                    (fun i _ k : nat => b i j k) ++ []) ++ [])))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    repeat (rewrite cat_empty in *).
                    apply cat_count_rev with (l1 := b 0 (S y) (S z) :: b 0 (S y) z
                    :: thread_set_1z 1 (S (S y)) z (fun x : ThreadId_t => x :: []) b) in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev with (l1 := b 0 y (S z) :: b 0 y z
                    :: thread_set_1z 1 (S y) z (fun x : ThreadId_t => x :: []) b) in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count with (l1 := b 0 (S y) (S z) :: b 0 (S y) z
                    :: thread_set_1z 1 1 z (fun x : ThreadId_t => x :: []) (fun i0 _ k : nat => b i0 (S y) k)).
                    rewrite block_ok_z in H0. rewrite block_ok_z. apply H0.
                    apply cat_count with (l1 := b 0 y (S z) :: b 0 y z
                    :: thread_set_1z 1 1 z (fun x : ThreadId_t => x :: []) (fun i0 _ k : nat => b i0 y k)).
                    rewrite block_ok_z in H1. rewrite block_ok_z. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction y.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev with (l1 := b 0 y (S z) :: b 0 y z
                        :: thread_set_1z 1 (S y) z (fun x : ThreadId_t => x :: []) b) in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count with (l1 := b 0 y (S z) :: b 0 y z
                        :: ((thread_set_1z 1 1 z (fun x : ThreadId_t => x :: []) (fun i0 _ k : nat => b i0 y k) ++
                        []) ++ [])).
                        repeat (rewrite cat_empty in *).
                        rewrite block_ok_z in H2. rewrite block_ok_z. apply H2.
                        apply IHy. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xy_block in H. simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** simpl in *. apply leb_correct in E. simpl in H0.
                    apply zip_buildlist_inclusion with (n := S (S y)) (f := (fun j : nat =>
                    (thread_set_3xyz (S (S x)) 1 1 (fun x : ThreadId_t => x :: [])
                    (fun i _ k : nat => b i j k))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) (S y) 0 :: b x (S y) 0
                    :: thread_set_2xz x (S (S y)) 1 (fun x0 : ThreadId_t => x0 :: []) b) in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev with (l1 := b (S x) y 0 :: b x y 0
                    :: thread_set_2xz x (S y) 1 (fun x0 : ThreadId_t => x0 :: []) b) in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count with (l1 := b (S x) (S y) 0 :: b x (S y) 0
                    :: thread_set_3xyz x 1 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 (S y) k)).
                    rewrite block_ok_xz in H0. rewrite block_ok_xyz. apply H0.
                    apply cat_count with (l1 := b (S x) y 0 :: b x y 0
                    :: thread_set_3xyz x 1 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k)).
                    rewrite block_ok_xz in H1. rewrite block_ok_xyz. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction y.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev with (l1 := b (S x) y 0 :: b x y 0
                        :: thread_set_2xz x (S y) 1 (fun x0 : ThreadId_t => x0 :: []) b) in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count with (l1 := b (S x) y 0 :: b x y 0
                        :: thread_set_3xyz x 1 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k)).
                        repeat (rewrite cat_empty in *).
                        rewrite block_ok_xz in H2. rewrite block_ok_xyz. apply H2.
                        apply IHy. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xy_block in H. simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S y)) (f := (fun j : nat =>
                    (thread_set_3xyz (S (S x)) 1 (S (S z)) (fun x : ThreadId_t => x :: [])
                    (fun i _ k : nat => b i j k))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) (S y) (S z) :: b (S x) (S y) z
                    :: (thread_set_1z (S (S x)) (S (S y)) z (fun x0 : ThreadId_t => x0 :: []) b ++
                    b x (S y) (S z) :: b x (S y) z
                    :: thread_set_1z (S x) (S (S y)) z (fun x0 : ThreadId_t => x0 :: []) b ++
                    thread_set_2xz x (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b)) in H.
                    destruct H as [m1 [m2 [H0 [H1 H']]]]; subst.
                    simpl.
                    apply cat_count with (l1 := b (S x) (S y) (S z) :: b (S x) (S y) z
                    :: ((thread_set_1z (S (S x)) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 (S y) k) ++ []) ++
                    b x (S y) (S z) :: b x (S y) z
                    :: (thread_set_1z (S x) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 (S y) k) ++ []) ++
                    thread_set_3xyz x 1 (S (S z)) (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 (S y) k))).
                    repeat (rewrite cat_empty).
                    apply cat_count_rev with (l1 := b (S x) (S y) (S z) :: b (S x) (S y) z
                    :: thread_set_1z (S (S x)) (S (S y)) z (fun x0 : ThreadId_t => x0 :: []) b) in H0.
                    destruct H0 as [m0 [m0' [H0 [H0' H']]]]; subst.
                    repeat (rewrite block_ok_z in *).
                    apply cat_count with (l1 := b (S x) (S y) (S z) :: b (S x) (S y) z
                    :: buildList z (fun k : nat => b (S x) (S y) k)).
                    apply H0. clear H0.
                    apply cat_count_rev with (l1 := b x (S y) (S z) :: b x (S y) z
                    :: buildList z (fun k : nat => b x (S y) k)) in H0'.
                    destruct H0' as [m00 [m00' [H0 [H0' H']]]]; subst.
                    apply cat_count with (l1 := b x (S y) (S z) :: b x (S y) z
                    :: buildList z (fun k : nat => b x (S y) k)).
                    apply H0.
                    clear H0. apply transpose_xy_block.
                    rewrite block_ok_yxz. rewrite block_ok_xz in H0'.
                    simpl. rewrite cat_empty. apply H0'.
                    clear H0.
                    apply cat_count_rev with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: (thread_set_1z (S (S x)) (S y) z (fun x0 : ThreadId_t => x0 :: []) b ++
                    b x y (S z) :: b x y z
                    :: thread_set_1z (S x) (S y) z (fun x0 : ThreadId_t => x0 :: []) b ++
                    thread_set_2xz x (S y) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b)) in H1.
                    destruct H1 as [m3 [m4 [H0 [H1 H']]]]; subst.
                    apply cat_count with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: ((thread_set_1z (S (S x)) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k) ++ []) ++
                    b x y (S z) :: b x y z
                    :: (thread_set_1z (S x) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k) ++ []) ++
                    thread_set_3xyz x 1 (S (S z)) (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k))).
                    repeat (rewrite cat_empty).
                    apply cat_count_rev with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: thread_set_1z (S (S x)) (S y) z (fun x0 : ThreadId_t => x0 :: []) b) in H0.
                    destruct H0 as [m0 [m0' [H0 [H0' H']]]]; subst.
                    repeat (rewrite block_ok_z in *).
                    apply cat_count with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: buildList z (fun k : nat => b (S x) y k)).
                    apply H0. clear H0.
                    apply cat_count_rev with (l1 := b x y (S z) :: b x y z
                    :: buildList z (fun k : nat => b x y k)) in H0'.
                    destruct H0' as [m00 [m00' [H0 [H0' H']]]]; subst.
                    apply cat_count with (l1 := b x y (S z) :: b x y z
                    :: buildList z (fun k : nat => b x y k)).
                    apply H0.
                    clear H0. apply transpose_xy_block.
                    rewrite block_ok_yxz. rewrite block_ok_xz in H0'.
                    simpl. rewrite cat_empty. apply H0'.
                    clear H0.
                    generalize dependent m4. induction y.
                    --- intros. apply H1.
                    --- simpl. intros.
                    apply cat_count_rev with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: (thread_set_1z (S (S x)) (S y) z (fun x0 : ThreadId_t => x0 :: []) b ++
                    b x y (S z) :: b x y z
                    :: thread_set_1z (S x) (S y) z (fun x0 : ThreadId_t => x0 :: []) b ++
                    thread_set_2xz x (S y) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b)) in H1.
                    destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
                    apply cat_count with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: ((thread_set_1z (S (S x)) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k) ++ []) ++
                    b x y (S z) :: b x y z
                    :: (thread_set_1z (S x) 1 z (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k) ++ []) ++
                    thread_set_3xyz x 1 (S (S z)) (fun x0 : ThreadId_t => x0 :: []) (fun i0 _ k : nat => b i0 y k))).
                    repeat (rewrite cat_empty).
                    apply cat_count_rev with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: thread_set_1z (S (S x)) (S y) z (fun x0 : ThreadId_t => x0 :: []) b) in H1.
                    destruct H1 as [m0 [m0' [H0 [H0' H']]]]; subst.
                    repeat (rewrite block_ok_z in *).
                    apply cat_count with (l1 := b (S x) y (S z) :: b (S x) y z
                    :: buildList z (fun k : nat => b (S x) y k)).
                    apply H0. clear H0.
                    apply cat_count_rev with (l1 := b x y (S z) :: b x y z
                    :: buildList z (fun k : nat => b x y k)) in H0'.
                    destruct H0' as [m00 [m00' [H0 [H0' H']]]]; subst.
                    apply cat_count with (l1 := b x y (S z) :: b x y z
                    :: buildList z (fun k : nat => b x y k)).
                    apply H0.
                    clear H0. apply transpose_xy_block.
                    rewrite block_ok_yxz. rewrite block_ok_xz in H0'.
                    simpl. rewrite cat_empty. apply H0'.
                    clear H1.
                    apply IHy. apply H2.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
      + destruct z.
        * simpl in *; destruct x,y; try (destruct x); try (destruct y); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
        * destruct z.
          ** simpl in *; destruct x,y; try (destruct x); try (destruct y); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
          ** simpl in *. destruct x,y.
            ++ destruct (r <=? S (S z)) eqn: E. simpl in H0.
            clear E. clear H. induction (r - l). inversion H0. apply le_0_n. apply IHn in H0. apply H0.
            inversion H0; apply le_0_n.
            ++ destruct y; destruct (r <=? S (S z)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x; destruct (r <=? S (S z)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x,y.
              -- simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** apply leb_correct in E.
                repeat (rewrite cat_empty in *).
                assert (count i (buildList (S (S z)) (fun k => b 0 0 k)) m).
                rewrite <- block_ok_z. apply H. simpl in *.
                apply zip_buildlist_inclusion with (n := S (S z)) (f := fun i => b 0 0 i :: []) (m := m) in H0.
                apply H0. apply E.
                clear H. clear E. clear H0. generalize dependent m. induction z. intros. apply H1.
                intros. inversion H1; subst. simpl.
                  apply cons_eq. apply IHz. apply H4.
                  apply cons_neq. apply IHz. apply H4. apply Hneq.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xz_block in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S z)) (f := (fun k : nat =>
                    (thread_set_2yz 1 (S (S y)) 1 (fun x : ThreadId_t => x :: [])
                    (fun i j _ : nat => b i j k) ++ [])))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    repeat (rewrite cat_empty in *).
                    apply cat_count_rev with (l1 := b 0 (S y) (S z) :: b 0 y (S z)
                    :: thread_set_1y 1 y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev with (l1 := b 0 (S y) z :: b 0 y z
                    :: thread_set_1y 1 y (S z) (fun x0 : ThreadId_t => x0 :: []) b) in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count with (l1 := b 0 (S y) (S z) :: b 0 y (S z)
                    :: thread_set_2yz 1 y 1 (fun x : ThreadId_t => x :: []) (fun i0 j _ : nat => b i0 j (S z))).
                    rewrite block_ok_y in H0. rewrite block_ok_yz.
                    clear H1. clear H2.
                    generalize dependent m1. induction y.
                      intros. apply H0.
                      intros. inversion H0; subst. simpl.
                        apply cons_eq. apply IHy. apply H4.
                        apply cons_neq. apply IHy. apply H4. apply Hneq.
                    apply cat_count with (l1 := b 0 (S y) z :: b 0 y z
                    :: thread_set_2yz 1 y 1 (fun x : ThreadId_t => x :: []) (fun i0 j _ : nat => b i0 j z)).
                    rewrite block_ok_y in H1. rewrite block_ok_yz.
                    clear H0. clear H2.
                    generalize dependent m3. induction y.
                      intros. apply H1.
                      intros. inversion H1; subst. simpl.
                        apply cons_eq. apply IHy. apply H4.
                        apply cons_neq. apply IHy. apply H4. apply Hneq.
                    clear H0. clear H1.
                    generalize dependent m4. induction z.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev with (l1 := b 0 (S y) z :: b 0 y z
                        :: (thread_set_1y 1 y (S z) (fun x0 : ThreadId_t => x0 :: []) b ++ [])) in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count with (l1 := b 0 (S y) z :: b 0 y z
                        :: (thread_set_2yz 1 y 1 (fun x : ThreadId_t => x :: []) (fun i0 j _ : nat => b i0 j z) ++
                        [])).
                        repeat (rewrite cat_empty in *).
                        rewrite block_ok_y in H2. rewrite block_ok_yz.
                        clear IHz. clear H3.
                        generalize dependent m5. induction y.
                          intros. apply H2.
                          intros. inversion H2; subst. simpl.
                            apply cons_eq. apply IHy. apply H4.
                            apply cons_neq. apply IHy. apply H4. apply Hneq.
                        apply IHz. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xz_block in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** simpl in *. apply leb_correct in E. simpl in H0.
                    apply zip_buildlist_inclusion with (n := S (S z)) (f := (fun k : nat =>
                    (thread_set_3xyz (S (S x)) 1 1 (fun x : ThreadId_t => x :: [])
                    (fun i j _ : nat => b i j k))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) 0 (S z) :: b x 0 (S z)
                    :: thread_set_2xy x 1 (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev with (l1 := b (S x) 0 z :: b x 0 z
                    :: thread_set_2xy x 1 (S z) (fun x0 : ThreadId_t => x0 :: []) b) in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count with (l1 := b (S x) 0 (S z) :: b x 0 (S z)
                    :: thread_set_3xyz x 1 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j (S z))).
                    rewrite block_ok_xy in H0. rewrite block_ok_xyz. apply H0.
                    apply cat_count with (l1 := b (S x) 0 z :: b x 0 z
                    :: thread_set_3xyz x 1 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z)).
                    rewrite block_ok_xy in H1. rewrite block_ok_xyz. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction z.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev with (l1 := b (S x) 0 z :: b x 0 z
                        :: thread_set_2xy x 1 (S z) (fun x0 : ThreadId_t => x0 :: []) b) in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count with (l1 := b (S x) 0 z :: b x 0 z
                        :: thread_set_3xyz x 1 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z)).
                        repeat (rewrite cat_empty in *).
                        rewrite block_ok_xy in H2. rewrite block_ok_xyz. apply H2.
                        apply IHz. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xz_block in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S z)) (f := (fun k : nat =>
                    (thread_set_3xyz (S (S x)) (S (S y)) 1 (fun x : ThreadId_t => x :: [])
                    (fun i j _ : nat => b i j k))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev with (l1 := b (S x) (S y) (S z) :: b (S x) y (S z)
                    :: (thread_set_1y (S (S x)) y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b ++
                    b x (S y) (S z) :: b x y (S z)
                    :: thread_set_1y (S x) y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b ++
                    thread_set_2xy x (S (S y)) (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b)) in H.
                    destruct H as [m1 [m2 [H0 [H1 H']]]]; subst.
                    simpl.
                    apply cat_count with (l1 := b (S x) (S y) (S z) :: b (S x) y (S z)
                    :: (thread_set_2yz (S (S x)) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j (S z)) ++
                    b x (S y) (S z) :: b x y (S z)
                    :: thread_set_2yz (S x) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j (S z)) ++
                    thread_set_3xyz x (S (S y)) 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j (S z)))).
                    repeat (rewrite cat_empty).
                    apply cat_count_rev with (l1 :=b (S x) (S y) (S z) :: b (S x) y (S z)
                    :: thread_set_1y (S (S x)) y (S (S z)) (fun x0 : ThreadId_t => x0 :: []) b) in H0.
                    destruct H0 as [m0 [m0' [H0 [H0' H']]]]; subst.
                    repeat (rewrite block_ok_y in *). repeat (rewrite block_ok_yz in *).
                    apply cat_count with (l1 := b (S x) (S y) (S z) :: b (S x) y (S z)
                    :: zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b (S x) j (S z))))).
                    clear H0'. clear H1.
                    assert (zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b (S x) j (S z))))
                        = buildList y (fun k : nat => b (S x) k (S z))). clear.
                      induction y. reflexivity. simpl. rewrite <- IHy. reflexivity.
                    rewrite H.
                    apply H0. clear H0.
                    apply cat_count_rev with (l1 := b x (S y) (S z) :: b x y (S z)
                    :: buildList y (fun k : nat => b x k (S z))) in H0'.
                    destruct H0' as [m00 [m00' [H0 [H0' H']]]]; subst.
                    apply cat_count with (l1 := b x (S y) (S z) :: b x y (S z)
                    :: zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b x j (S z))))).
                    assert (zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b x j (S z))))
                        = buildList y (fun k : nat => b x k (S z))). clear.
                      induction y. reflexivity. simpl. rewrite <- IHy. reflexivity.
                    rewrite H.
                    apply H0.
                    clear H0. apply transpose_xz_block.
                    rewrite block_ok_zxy. rewrite block_ok_xy in H0'.
                    simpl. rewrite cat_empty. apply H0'.
                    clear H0.
                    apply cat_count_rev with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: (thread_set_1y (S (S x)) y (S z) (fun x0 : ThreadId_t => x0 :: []) b ++
                    b x (S y) z :: b x y z
                    :: thread_set_1y (S x) y (S z) (fun x0 : ThreadId_t => x0 :: []) b ++
                     thread_set_2xy x (S (S y)) (S z) (fun x0 : ThreadId_t => x0 :: []) b)) in H1.
                    destruct H1 as [m3 [m4 [H0 [H1 H']]]]; subst.
                    apply cat_count with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: (thread_set_2yz (S (S x)) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z) ++
                    b x (S y) z :: b x y z
                    :: thread_set_2yz (S x) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z) ++
                    thread_set_3xyz x (S (S y)) 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z))).
                    repeat (rewrite cat_empty).
                    apply cat_count_rev with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: thread_set_1y (S (S x)) y (S z) (fun x0 : ThreadId_t => x0 :: []) b) in H0.
                    destruct H0 as [m0 [m0' [H0 [H0' H']]]]; subst.
                    repeat (rewrite block_ok_y in *).
                    repeat (rewrite block_ok_yz in *).
                    repeat (rewrite block_ok_xy in *).
                    apply cat_count with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b (S x) j z)))).
                    assert (zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b (S x) j z)))
                        = buildList y (fun k : nat => b (S x) k z)). clear.
                      induction y. reflexivity. simpl. rewrite <- IHy. reflexivity.
                    rewrite H.
                    apply H0. clear H0.
                    apply cat_count_rev with (l1 := b x (S y) z :: b x y z
                    :: buildList y (fun k : nat => b x k z)) in H0'.
                    destruct H0' as [m00 [m00' [H0 [H0' H']]]]; subst.
                    apply cat_count with (l1 := b x (S y) z :: b x y z
                    :: zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b x j z)))).
                    assert (zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b x j z)))
                        = buildList y (fun k : nat => b x k z)). clear.
                      induction y. reflexivity. simpl. rewrite <- IHy. reflexivity.
                    rewrite H.
                    apply H0. clear H0.
                    apply transpose_xz_block.
                    rewrite block_ok_zxy.
                    simpl. rewrite cat_empty. apply H0'.
                    clear H0.
                    generalize dependent m4. induction z.
                    --- intros. apply H1.
                    --- simpl. intros.
                    apply cat_count_rev with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: (thread_set_1y (S (S x)) y (S z) (fun x0 : ThreadId_t => x0 :: []) b ++
                    b x (S y) z :: b x y z
                    :: thread_set_1y (S x) y (S z) (fun x0 : ThreadId_t => x0 :: []) b ++
                    thread_set_2xy x (S (S y)) (S z) (fun x0 : ThreadId_t => x0 :: []) b)) in H1.
                    destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
                    apply cat_count with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: (thread_set_2yz (S (S x)) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z) ++
                    b x (S y) z :: b x y z
                    :: thread_set_2yz (S x) y 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z) ++
                    thread_set_3xyz x (S (S y)) 1 (fun x0 : ThreadId_t => x0 :: []) (fun i0 j _ : nat => b i0 j z))).
                    repeat (rewrite cat_empty).
                    apply cat_count_rev with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: thread_set_1y (S (S x)) y (S z) (fun x0 : ThreadId_t => x0 :: []) b) in H1.
                    destruct H1 as [m0 [m0' [H0 [H0' H']]]]; subst.
                    repeat (rewrite block_ok_y in *).
                    repeat (rewrite block_ok_yz in *).
                    repeat (rewrite block_ok_xy in *).
                    apply cat_count with (l1 := b (S x) (S y) z :: b (S x) y z
                    :: zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b (S x) j z)))).
                    assert (zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b (S x) j z)))
                        = buildList y (fun k : nat => b (S x) k z)). clear.
                      induction y. reflexivity. simpl. rewrite <- IHy. reflexivity.
                    rewrite H.
                    apply H0. clear H0.
                    apply cat_count_rev with (l1 := b x (S y) z :: b x y z
                    :: buildList y (fun k : nat => b x k z)) in H0'.
                    destruct H0' as [m00 [m00' [H0 [H0' H']]]]; subst.
                    apply cat_count with (l1 := b x (S y) z :: b x y z
                    :: zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b x j z)))).
                    assert (zip (buildList y (fun j : nat => buildList 1 (fun _ : nat => b x j z)))
                        = buildList y (fun k : nat => b x k z)). clear.
                      induction y. reflexivity. simpl. rewrite <- IHy. reflexivity.
                    rewrite H.
                    apply H0. clear H0.
                    apply transpose_xz_block.
                    rewrite block_ok_zxy.
                    simpl. rewrite cat_empty. apply H0'.
                    clear H1.
                    apply IHz. apply H2.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
  - destruct shp as [p z]. destruct p as [x y]. destruct shp' as [p z']. destruct p as [x' y'].
    destruct d.
      + destruct x.
        * simpl in *; destruct y,z; try (destruct y); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
        * destruct x.
          ** simpl in *; destruct y,z; try (destruct y); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
          ** simpl in *. destruct y,z.
            ++ destruct (r <=? S (S x)) eqn: E. simpl in H0.
            clear E. clear H. induction (r - l). inversion H0. apply le_0_n. apply IHn in H0. apply H0.
            inversion H0; apply le_0_n.
            ++ destruct z; destruct (r <=? S (S x)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct y; destruct (r <=? S (S x)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct y,z.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** apply leb_correct in E.
                assert (count i (zip (buildList (S (S x)) (fun i => zip (buildList 1 (fun j => zip (buildList 1 (fun k : nat =>
                  thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k)))))))) m).
                rewrite <- grid_ok_xyz. apply H. simpl in *.
                apply zip_buildlist_inclusion with (n := S (S x)) (f := fun i => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) (g i 0 0)) (m := m) in H0.
                apply H0. apply E. clear H0. clear E. clear H. simpl.
                repeat (rewrite cat_empty in H1).
                apply cat_count_rev in H1.
                destruct H1 as [m1 [m2 [H1 [H2 H']]]]; subst.
                apply cat_count_rev in H2.
                destruct H2 as [m3 [m4 [H2 [H3 H']]]]; subst.
                apply cat_count. apply H1.
                apply cat_count. apply H2.
                clear H1. clear H2. generalize dependent m4.
                induction x.
                  intros. apply H3.
                  intros. simpl in *. apply cat_count_rev in H3.
                  destruct H3 as [m5 [m6 [H1 [H2 H']]]]; subst.
                  apply cat_count. repeat (rewrite cat_empty in H1). apply H1. apply IHx. apply H2. 
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S x)) (f := (fun i : nat =>
                    ((thread_set_1z 1 1 (S (S z)) (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun _ j k : nat => g i j k)) ++ []) ++ []))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count.
                    rewrite grid_ok_z in H0. rewrite grid_ok_z. apply H0.
                    apply cat_count.
                    rewrite grid_ok_z in H1. rewrite grid_ok_z. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction x.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty in *).
                        rewrite grid_ok_z in H2. rewrite grid_ok_z. apply H2.
                        apply IHx. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S x)) (f := (fun i : nat =>
                    ((thread_set_2yz 1 (S (S y)) 1 (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun _ j k : nat => g i j k)) ++ [])))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count.
                    rewrite grid_ok_yz in H0. rewrite grid_ok_yz. apply H0.
                    apply cat_count.
                    rewrite grid_ok_yz in H1. rewrite grid_ok_yz. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction x.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty in *).
                        rewrite grid_ok_yz in H2. rewrite grid_ok_yz. apply H2.
                        apply IHx. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S x)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S x)) (f := ((fun i : nat =>
                    (thread_set_2yz 1 (S (S y)) (S (S z)) (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun _ j k : nat => g i j k)) ++ [])))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H']]]]; subst.
                    simpl.
                    apply cat_count.
                    repeat (rewrite cat_empty). repeat (rewrite grid_ok_z in *).
                    repeat (rewrite grid_ok_yz in *). apply H0.
                    clear H0.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H0 [H1 H']]]]; subst.
                    apply cat_count.
                    repeat (rewrite cat_empty). repeat (rewrite grid_ok_z in *).
                    repeat (rewrite grid_ok_yz in *). apply H0.
                    clear H0.
                    generalize dependent m4. induction x.
                    --- intros. apply H1.
                    --- simpl. intros.
                    apply cat_count_rev in H1.
                    destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
                    apply cat_count.
                    repeat (rewrite cat_empty). repeat (rewrite grid_ok_z in *).
                    repeat (rewrite grid_ok_yz in *). apply H1.
                    clear H1. apply IHx. apply H2.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
      + destruct y.
        * simpl in *; destruct x,z; try (destruct x); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
        * destruct y.
          ** simpl in *; destruct x,z; try (destruct x); try (destruct z); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
          ** simpl in *. destruct x,z.
            ++ destruct (r <=? S (S y)) eqn: E. simpl in H0.
            clear E. clear H. induction (r - l). inversion H0. apply le_0_n. apply IHn in H0. apply H0.
            inversion H0; apply le_0_n.
            ++ destruct z; destruct (r <=? S (S y)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x; destruct (r <=? S (S y)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x,z.
              -- apply transpose_xy_grid in H. simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** apply leb_correct in E.
                assert (count i (zip (buildList (S (S y)) (fun j => zip (buildList 1 (fun i => zip (buildList 1 (fun k : nat =>
                  thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k)))))))) m).
                rewrite <- grid_ok_yxz. apply H. simpl in *.
                apply zip_buildlist_inclusion with (n := S (S y)) (f := fun j => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) (g 0 j 0)) (m := m) in H0.
                apply H0. apply E. clear H0. clear E. clear H. simpl.
                repeat (rewrite cat_empty in H1).
                apply cat_count_rev in H1.
                destruct H1 as [m1 [m2 [H1 [H2 H']]]]; subst.
                apply cat_count_rev in H2.
                destruct H2 as [m3 [m4 [H2 [H3 H']]]]; subst.
                apply cat_count. apply H1.
                apply cat_count. apply H2.
                clear H1. clear H2. generalize dependent m4.
                induction y.
                  intros. apply H3.
                  intros. simpl in *. apply cat_count_rev in H3.
                  destruct H3 as [m5 [m6 [H1 [H2 H']]]]; subst.
                  apply cat_count. repeat (rewrite cat_empty in H1). apply H1. apply IHy. apply H2. 
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    repeat (rewrite cat_empty in *).
                    apply zip_buildlist_inclusion with (n := S (S y)) (f := (fun j : nat =>
                    ((thread_set_1z 1 1 (S (S z)) (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun i _ k : nat => g i j k)) ++ []) ++ []))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count.
                    rewrite grid_ok_z in H0. rewrite grid_ok_z. apply H0.
                    apply cat_count.
                    rewrite grid_ok_z in H1. rewrite grid_ok_z. apply H1.
                    clear H0. clear H1.
                    generalize dependent m4. induction y.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty in *).
                        rewrite grid_ok_z in H2. rewrite grid_ok_z. apply H2.
                        apply IHy. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xy_grid in H. simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S y)) (f := (fun j : nat =>
                    ((thread_set_3xyz (S (S x)) 1 1 (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun i _ k : nat => g i j k)))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count.
                    rewrite grid_ok_xz in H0. rewrite grid_ok_xyz.
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H1. clear H2. clear H0'.
                    generalize dependent m4'. induction x.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHx. apply H1'.
                    apply cat_count.
                    rewrite grid_ok_xz in H1. rewrite grid_ok_xyz.
                    apply cat_count_rev in H1.
                    destruct H1 as [m1' [m2' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0. clear H2. clear H0'.
                    generalize dependent m4'. induction x.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHx. apply H1'.
                    clear H0. clear H1.
                    generalize dependent m4. induction y.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty in *).
                        rewrite grid_ok_xz in H2. rewrite grid_ok_xyz.
                        apply cat_count_rev in H2.
                        destruct H2 as [m1' [m2' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3' [m4' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'. clear H3. clear IHy.
                        generalize dependent m4'. induction x.
                          intros. apply H1'.
                          intros. simpl in *. apply cat_count_rev in H1'.
                          repeat (rewrite cat_empty in *).
                          destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                          apply cat_count. apply H0'.
                          apply IHx. apply H1'.
                        apply IHy. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xy_grid in H. simpl in *. destruct (r <=? S (S y)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S y)) (f := ((fun j : nat =>
                    (thread_set_3xyz (S (S x)) 1 (S (S z)) (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun i _ k : nat => g i j k)))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H']]]]; subst.
                    simpl.
                    apply cat_count.
                    repeat (rewrite cat_empty). clear H1. repeat (rewrite grid_ok_z in *).
                    repeat (rewrite grid_ok_xz in *). repeat (rewrite grid_ok_xyz in *).
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0'. generalize dependent m4'.
                    induction x.
                      intros. apply H1'.
                      intros. apply cat_count_rev in H1'.
                      destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                      simpl in *. repeat (rewrite cat_empty in *).
                      apply cat_count. apply H0''. apply IHx. apply H1''.
                    apply cat_count_rev in H1.
                    clear H0.
                    destruct H1 as [m3 [m4 [H0 [H1 H']]]]; subst.
                    apply cat_count.
                    repeat (rewrite cat_empty). clear H1. repeat (rewrite grid_ok_z in *).
                    repeat (rewrite grid_ok_xz in *). repeat (rewrite grid_ok_xyz in *).
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0'. generalize dependent m4'.
                    induction x.
                      intros. apply H1'.
                      intros. apply cat_count_rev in H1'.
                      destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                      simpl in *. repeat (rewrite cat_empty in *).
                      apply cat_count. apply H0''. apply IHx. apply H1''.
                    clear H0.
                    generalize dependent m4. induction y.
                    --- intros. apply H1.
                    --- simpl. intros.
                        apply cat_count_rev in H1.
                        destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty). clear H2. repeat (rewrite grid_ok_z in *).
                        repeat (rewrite grid_ok_xz in *). repeat (rewrite grid_ok_xyz in *).
                        apply cat_count_rev in H1.
                        destruct H1 as [m1'' [m2'' [H0' [H1' H']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'. clear IHy. generalize dependent m4'.
                        induction x.
                          intros. apply H1'.
                          intros. apply cat_count_rev in H1'.
                          destruct H1' as [m1''' [m2''' [H0'' [H1'' H']]]]; subst.
                          simpl in *. repeat (rewrite cat_empty in *).
                          apply cat_count. apply H0''. apply IHx. apply H1''.
                        clear H1. apply IHy. apply H2.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
      + destruct z.
        * simpl in *; destruct x,y; try (destruct x); try (destruct y); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
        * destruct z.
          ** simpl in *; destruct x,y; try (destruct x); try (destruct y); destruct (r <=? 0) eqn: E;
          try (apply leb_correct in E; inversion E; subst; simpl in *);
          inversion H0; apply le_0_n.
          ** simpl in *. destruct x,y.
            ++ destruct (r <=? S (S z)) eqn: E. simpl in H0.
            clear E. clear H. induction (r - l). inversion H0. apply le_0_n. apply IHn in H0. apply H0.
            inversion H0; apply le_0_n.
            ++ destruct y; destruct (r <=? S (S z)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x; destruct (r <=? S (S z)); simpl in H0;
            try (clear H; induction (r - l); try (inversion H0; apply le_0_n); apply IHn in H0; apply H0).
            ++ destruct x,y.
              -- apply transpose_xz_grid in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** apply leb_correct in E.
                assert (count i (zip (buildList (S (S z)) (fun k => zip (buildList 1 (fun i => zip (buildList 1 (fun j : nat =>
                  thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k)))))))) m).
                rewrite <- grid_ok_zxy. apply H. simpl in *.
                apply zip_buildlist_inclusion with (n := S (S z)) (f := fun k => thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) (g 0 0 k)) (m := m) in H0.
                apply H0. apply E. clear H0. clear E. clear H. simpl.
                repeat (rewrite cat_empty in H1).
                apply cat_count_rev in H1.
                destruct H1 as [m1 [m2 [H1 [H2 H']]]]; subst.
                apply cat_count_rev in H2.
                destruct H2 as [m3 [m4 [H2 [H3 H']]]]; subst.
                apply cat_count. apply H1.
                apply cat_count. apply H2.
                clear H1. clear H2. generalize dependent m4.
                induction z.
                  intros. apply H3.
                  intros. simpl in *. apply cat_count_rev in H3.
                  destruct H3 as [m5 [m6 [H1 [H2 H']]]]; subst.
                  apply cat_count. repeat (rewrite cat_empty in H1). apply H1. apply IHz. apply H2. 
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xz_grid in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    repeat (rewrite cat_empty in *).
                    apply zip_buildlist_inclusion with (n := S (S z)) (f := (fun k : nat =>
                    ((thread_set_2yz 1 (S (S y)) 1 (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun i j _ : nat => g i j k)) ++ [])))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count.
                    clear H1. clear H2.
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    rewrite grid_ok_yz. rewrite grid_ok_y in H1'.
                    generalize dependent m4'. induction y.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                      apply cat_count. rewrite cat_empty. apply H0''. apply IHy. apply H1''.
                    clear H0.
                    apply cat_count.
                    clear H2.
                    apply cat_count_rev in H1.
                    destruct H1 as [m1' [m2' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    rewrite grid_ok_yz. rewrite grid_ok_y in H1'.
                    generalize dependent m4'. induction y.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                      apply cat_count. rewrite cat_empty. apply H0''. apply IHy. apply H1''.
                    clear H1.
                    generalize dependent m4. induction z.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty in *).
                        apply cat_count_rev in H2.
                        destruct H2 as [m1' [m2' [H0' [H1' H']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        rewrite grid_ok_yz. rewrite grid_ok_y in H1'.
                        generalize dependent m4'. clear H3. clear IHz. induction y.
                          intros. apply H1'.
                          intros. simpl in *. apply cat_count_rev in H1'.
                          destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                          apply cat_count. rewrite cat_empty. apply H0''. apply IHy. apply H1''.
                        apply IHz. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xz_grid in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S z)) (f := (fun k : nat =>
                    ((thread_set_3xyz (S (S x)) 1 1 (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun i j _ : nat => g i j k)))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H2]]]]; subst.
                    apply cat_count_rev in H1.
                    destruct H1 as [m3 [m4 [H1 [H2 H3]]]]; subst.
                    simpl. repeat (rewrite cat_empty in *).
                    apply cat_count.
                    rewrite grid_ok_xy in H0. rewrite grid_ok_xyz.
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H1. clear H2. clear H0'.
                    generalize dependent m4'. induction x.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHx. apply H1'.
                    apply cat_count.
                    rewrite grid_ok_xy in H1. rewrite grid_ok_xyz.
                    apply cat_count_rev in H1.
                    destruct H1 as [m1' [m2' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0. clear H2. clear H0'.
                    generalize dependent m4'. induction x.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHx. apply H1'.
                    clear H0. clear H1.
                    generalize dependent m4. induction z.
                    +++ intros. apply H2.
                    +++ intros. simpl in *.
                        apply cat_count_rev in H2.
                        destruct H2 as [m5 [m6 [H2 [H3 H4]]]]; subst.
                        apply cat_count.
                        repeat (rewrite cat_empty in *).
                        rewrite grid_ok_xy in H2. rewrite grid_ok_xyz.
                        apply cat_count_rev in H2.
                        destruct H2 as [m1' [m2' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3' [m4' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'. clear H3. clear IHz.
                        generalize dependent m4'. induction x.
                          intros. apply H1'.
                          intros. simpl in *. apply cat_count_rev in H1'.
                          repeat (rewrite cat_empty in *).
                          destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                          apply cat_count. apply H0'.
                          apply IHx. apply H1'.
                        apply IHz. apply H3.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
              -- apply transpose_xz_grid in H. simpl in *. destruct (r <=? S (S z)) eqn: E.
                *** simpl in *. apply leb_correct in E.
                    apply zip_buildlist_inclusion with (n := S (S z)) (f := ((fun k : nat =>
                    (thread_set_3xyz (S (S x)) (S (S y)) 1 (fun b : nat -> nat -> nat -> ThreadId_t =>
                    thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) (fun i j _ : nat => g i j k)))))
                    (m := m) (i := i) (a := l) (m' := m') in H0.
                    apply H0. apply E.
                    clear E. clear H0.
                    apply cat_count_rev in H.
                    destruct H as [m1 [m2 [H0 [H1 H']]]]; subst.
                    simpl.
                    apply cat_count.
                    repeat (rewrite cat_empty). clear H1. repeat (rewrite grid_ok_y in *).
                    repeat (rewrite grid_ok_xy in *). repeat (rewrite grid_ok_xyz in *).
                    repeat (rewrite grid_ok_yz in *).
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H']]]]; subst.
                    apply cat_count.
                    clear H1'.
                    apply cat_count_rev in H0'.
                    destruct H0' as [m1'' [m2'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3'' [m4'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0'.
                    generalize dependent m4''. induction y.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHy. apply H1'.
                    clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                    apply cat_count. clear H1'.
                    apply cat_count_rev in H0'.
                    destruct H0' as [m1'' [m2'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3'' [m4'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0'.
                    generalize dependent m4''. induction y.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHy. apply H1'.
                    clear H0'. generalize dependent m4'.
                    induction x.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                      simpl in *. repeat (rewrite cat_empty in *).
                      apply cat_count. clear H1''. clear IHx.
                        apply cat_count_rev in H0''.
                        destruct H0'' as [m3'' [m4'' [H0' [H1' H']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m5'' [m6'' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'.
                        generalize dependent m6''. induction y.
                          intros. apply H1'.
                          intros. simpl in *. repeat (rewrite cat_empty in *).
                          apply cat_count_rev in H1'.
                          destruct H1' as [m1''' [m2''' [H0' [H1' H2']]]]; subst.
                          apply cat_count. apply H0'. clear H0'.
                          apply IHy. apply H1'.
                      apply IHx. apply H1''.
                    apply cat_count_rev in H1.
                    clear H0.
                    destruct H1 as [m3 [m4 [H0 [H1 H']]]]; subst.
                    apply cat_count.
                    repeat (rewrite cat_empty). clear H1. repeat (rewrite grid_ok_y in *).
                    repeat (rewrite grid_ok_xy in *). repeat (rewrite grid_ok_xyz in *).
                    repeat (rewrite grid_ok_yz in *).
                    apply cat_count_rev in H0.
                    destruct H0 as [m1' [m2' [H0' [H1' H']]]]; subst.
                    apply cat_count.
                    clear H1'.
                    apply cat_count_rev in H0'.
                    destruct H0' as [m1'' [m2'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3'' [m4'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0'.
                    generalize dependent m4''. induction y.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHy. apply H1'.
                    clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                    apply cat_count. clear H1'.
                    apply cat_count_rev in H0'.
                    destruct H0' as [m1'' [m2'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'. clear H0'.
                    apply cat_count_rev in H1'.
                    destruct H1' as [m3'' [m4'' [H0' [H1' H2']]]]; subst.
                    apply cat_count. apply H0'.
                    clear H0'.
                    generalize dependent m4''. induction y.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      repeat (rewrite cat_empty in *).
                      destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                      apply cat_count. apply H0'.
                      apply IHy. apply H1'.
                    clear H0'. generalize dependent m4'.
                    induction x.
                      intros. apply H1'.
                      intros. simpl in *. apply cat_count_rev in H1'.
                      destruct H1' as [m1'' [m2'' [H0'' [H1'' H']]]]; subst.
                      simpl in *. repeat (rewrite cat_empty in *).
                      apply cat_count. clear H1''. clear IHx.
                        apply cat_count_rev in H0''.
                        destruct H0'' as [m3'' [m4'' [H0' [H1' H']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m5'' [m6'' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'.
                        generalize dependent m6''. induction y.
                          intros. apply H1'.
                          intros. simpl in *. repeat (rewrite cat_empty in *).
                          apply cat_count_rev in H1'.
                          destruct H1' as [m1''' [m2''' [H0' [H1' H2']]]]; subst.
                          apply cat_count. apply H0'. clear H0'.
                          apply IHy. apply H1'.
                      apply IHx. apply H1''.
                    clear H0.
                    generalize dependent m4. induction z.
                    --- intros. apply H1.
                    --- simpl. intros.
                        apply cat_count_rev in H1.
                        destruct H1 as [m1' [m2' [H1 [H2 H3]]]]; subst.
                        apply cat_count. clear H2.
                        repeat (rewrite cat_empty). repeat (rewrite grid_ok_y in *).
                        repeat (rewrite grid_ok_xy in *). repeat (rewrite grid_ok_xyz in *).
                        repeat (rewrite grid_ok_yz in *).
                        apply cat_count_rev in H1.
                        destruct H1 as [m1'' [m2'' [H0' [H1' H']]]]; subst.
                        apply cat_count.
                        clear H1'.
                        apply cat_count_rev in H0'.
                        destruct H0' as [m1''' [m2''' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3'' [m4'' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'.
                        generalize dependent m4''. clear IHz. induction y.
                          intros. apply H1'.
                          intros. simpl in *. apply cat_count_rev in H1'.
                          repeat (rewrite cat_empty in *).
                          destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                          apply cat_count. apply H0'.
                          apply IHy. apply H1'.
                        clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3' [m4' [H0' [H1' H']]]]; subst.
                        apply cat_count. clear H1'.
                        apply cat_count_rev in H0'.
                        destruct H0' as [m1''' [m2'' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'. clear H0'.
                        apply cat_count_rev in H1'.
                        destruct H1' as [m3''' [m4'' [H0' [H1' H2']]]]; subst.
                        apply cat_count. apply H0'.
                        clear H0'.
                        generalize dependent m4''. clear IHz. induction y.
                          intros. apply H1'.
                          intros. simpl in *. apply cat_count_rev in H1'.
                          repeat (rewrite cat_empty in *).
                          destruct H1' as [m5' [m6' [H0' [H1' H2']]]]; subst.
                          apply cat_count. apply H0'.
                          apply IHy. apply H1'.
                        clear H0'. clear IHz. generalize dependent m4'.
                        induction x.
                          intros. apply H1'.
                          intros. simpl in *. apply cat_count_rev in H1'.
                          destruct H1' as [m1''' [m2'' [H0'' [H1'' H']]]]; subst.
                          simpl in *. repeat (rewrite cat_empty in *).
                          apply cat_count. clear H1''. clear IHx.
                            apply cat_count_rev in H0''.
                            destruct H0'' as [m3'' [m4'' [H0' [H1' H']]]]; subst.
                            apply cat_count. apply H0'. clear H0'.
                            apply cat_count_rev in H1'.
                            destruct H1' as [m5'' [m6'' [H0' [H1' H2']]]]; subst.
                            apply cat_count. apply H0'.
                            clear H0'.
                            generalize dependent m6''. induction y.
                              intros. apply H1'.
                              intros. simpl in *. repeat (rewrite cat_empty in *).
                              apply cat_count_rev in H1'.
                              destruct H1' as [m1''' [m2''' [H0' [H1' H2']]]]; subst.
                              apply cat_count. apply H0'. clear H0'.
                              apply IHy. apply H1'.
                          apply IHx. apply H1''.
                        apply cat_count_rev in H1.
                        apply IHz. apply H2.
                *** simpl in H0. inversion H0; subst. apply le_0_n.
  - simpl in *. apply collection_ok_select with (n := n) (m := m) (m' := m') (l := l) (r := r) (d := d) in H.
    apply H. apply H0. apply H1.
  - inversion H0. apply le_0_n.
Qed.

