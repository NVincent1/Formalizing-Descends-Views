
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
              -- admit.
              -- admit.
      + admit.
      + admit.
  - admit.
  - simpl in *. apply collection_ok_select with (n := n) (m := m) (m' := m') (l := l) (r := r) (d := d) in H.
    apply H. apply H0. apply H1.
  - inversion H0. apply le_0_n.
Admitted.

