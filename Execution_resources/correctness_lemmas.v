
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Axiom FunEquality :
  forall T T' (f g : T -> T'),
  f = g <-> forall x, (f x) = (g x).

Lemma blockempty : 
  forall x T fj,
  (forall (j : nat), fj j = []) ->
  zip (buildList x (fun (j:nat) => (fj j : List T))) = [].
Proof.
  intros. induction x. reflexivity. simpl. rewrite H. apply IHx.
Qed.


Lemma block_ok_z :
forall b x y z,
thread_set_1z (S x) (S y) z (fun x0 : ThreadId_t => x0 :: []) b =
buildList z (fun k => b x y k).
Proof.
  induction z.
    + intros. reflexivity.
    + intros. simpl. rewrite IHz. reflexivity.
Qed.


Lemma block_ok_y :
forall b x y z,
thread_set_1y (S x) y (S z) (fun x0 : ThreadId_t => x0 :: []) b =
buildList y (fun k => b x k z).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl. rewrite IHy. reflexivity.
Qed.

Lemma block_ok_yz :
forall b x y z,
thread_set_2yz (S x) y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList y (fun j => (buildList z (fun k => b x j k)))).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. rewrite block_ok_z. rewrite IHy. reflexivity.
Qed.

Lemma block_ok_xz :
forall b x y z,
thread_set_2xz x (S y) z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList x (fun j => (buildList z (fun k => b j y k)))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. rewrite block_ok_z. rewrite IHx. reflexivity.
Qed.

Lemma block_ok_xy :
forall b x y z,
thread_set_2xy x y (S z) (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList x (fun j => (buildList y (fun k => b j k z)))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. rewrite block_ok_y. rewrite IHx. reflexivity.
Qed.

Lemma block_ok_xyz :
forall b x y z,
thread_set_3xyz x y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList x (fun i => (zip (buildList y (fun j => (buildList z (fun k => b i j k))))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y,z.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. rewrite blockempty. reflexivity. reflexivity. rewrite blockempty. simpl. rewrite blockempty in IHx. apply IHx. reflexivity. reflexivity.
      * simpl. rewrite block_ok_z. rewrite block_ok_yz. rewrite IHx. reflexivity.
Qed.

Lemma block_ok_yxz :
forall b x y z,
thread_set_3yxz x y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList y (fun j => (zip (buildList x (fun i => (buildList z (fun k => b i j k))))))).
Proof.
  induction y.
    + intros. destruct x; reflexivity.
    + intros. simpl in *.
    destruct x,z.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. rewrite blockempty. reflexivity. reflexivity. rewrite blockempty. simpl. rewrite blockempty in IHy. apply IHy. reflexivity. reflexivity.
      * simpl. rewrite block_ok_z. rewrite block_ok_xz. rewrite IHy. simpl. reflexivity.
Qed.

Lemma block_ok_zxy :
forall b z x y,
thread_set_3zxy x y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList z (fun k => (zip (buildList x (fun i => (buildList y (fun j => b i j k))))))).
Proof.
  induction z.
    + intros. destruct x,y; reflexivity.
    + intros. simpl in *.
    destruct x,y.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. rewrite blockempty. reflexivity. reflexivity. rewrite blockempty. simpl. rewrite blockempty in IHz. apply IHz. reflexivity. reflexivity.
      * simpl. rewrite block_ok_y. rewrite block_ok_xy. rewrite IHz. simpl. reflexivity.
Qed.

Lemma grid_ok_z :
forall g x y z x' y' z',
thread_set_1z (S x) (S y) z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g x y k))).
Proof.
  induction z.
    + intros. reflexivity.
    + intros. simpl. rewrite IHz. reflexivity.
Qed.

Lemma grid_ok_y :
forall g x y z x' y' z',
thread_set_1y (S x) y (S z)
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList y (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g x k z))).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl. rewrite IHy. reflexivity.
Qed.

Lemma grid_ok_yz :
forall g x y z x' y' z',
thread_set_2yz (S x) y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList y (fun j => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g x j k))))).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * intros. simpl. clear. induction y. reflexivity. apply IHy.
      * intros. simpl. rewrite grid_ok_z. rewrite IHy. reflexivity.
Qed.

Lemma grid_ok_xz :
forall g x y z x' y' z',
thread_set_2xz x (S y) z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList x (fun j => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g j y k))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * intros. simpl. clear. induction x. reflexivity. apply IHx.
      * intros. simpl. rewrite grid_ok_z. rewrite IHx. reflexivity.
Qed.

Lemma grid_ok_xy :
forall g x y z x' y' z',
thread_set_2xy x y (S z)
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList x (fun j => zip (buildList y (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g j k z))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y.
      * intros. simpl. clear. induction x. reflexivity. apply IHx.
      * intros. simpl. rewrite grid_ok_y. rewrite IHx. reflexivity.
Qed.

Lemma grid_ok_yxz :
forall g y x z x' y' z',
thread_set_3yxz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList y (fun j => zip (buildList x (fun i => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k))))))).
Proof.
  induction y.
    + intros. destruct x; reflexivity.
    + intros. simpl in *.
    destruct x,z.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. rewrite blockempty. reflexivity. reflexivity. rewrite blockempty. simpl. rewrite blockempty in IHy. apply IHy. reflexivity. reflexivity.
      * simpl. rewrite grid_ok_z. rewrite grid_ok_xz. rewrite IHy. reflexivity.
Qed.

Lemma grid_ok_xyz :
forall g x y z x' y' z',
thread_set_3xyz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList x (fun i => zip (buildList y (fun j => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k))))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y,z.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. rewrite blockempty. reflexivity. reflexivity. rewrite blockempty. simpl. rewrite blockempty in IHx. apply IHx. reflexivity. reflexivity.
      * simpl. rewrite grid_ok_z. rewrite grid_ok_yz. rewrite IHx. reflexivity.
Qed.

Lemma grid_ok_zxy :
forall g z x y x' y' z',
thread_set_3zxy x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList z (fun k => zip (buildList x (fun i => zip (buildList y (fun j : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k))))))).
Proof.
  induction z.
    + intros. destruct x,y; reflexivity.
    + intros. simpl in *.
    destruct x,y.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. rewrite blockempty. reflexivity. reflexivity. rewrite blockempty. simpl. rewrite blockempty in IHz. apply IHz. reflexivity. reflexivity.
      * simpl. rewrite grid_ok_y. rewrite grid_ok_xy. rewrite IHz. reflexivity.
Qed.

Lemma zip_ok :
  forall T x (fi : nat -> T),
    zip (buildList x (fun i : nat => fi i :: [])) =
    buildList x (fun i : nat => fi i).
Proof.
  induction x.
  - reflexivity.
  - simpl. intros. rewrite IHx. reflexivity.
Qed.

Lemma zip_count :
  forall T (a : T) x (fi : nat -> T) n,
    count a (zip (buildList x (fun i : nat => fi i :: []))) n <->
    count a (buildList x (fun i : nat => fi i)) n.
Proof.
  intros. split; rewrite zip_ok; intro H; apply H.
Qed.

Lemma transpose_lemma :
forall T (a:T) x y n f,
count a (zip (buildList y (fun j => (zip (buildList x (fun i => f i j)))))) n ->
count a (zip (buildList x (fun i => (zip (buildList y (fun j => f i j)))))) n.
Proof.
  induction y.
  - intros. induction x. apply H. apply IHx in H. apply H.
  - simpl in *. intros. apply cat_count_rev in H.
  destruct H as [m [m' [H [H' H2]]]]. subst.
  apply IHy in H'. clear IHy.
  generalize dependent m.
  generalize dependent m'.
  induction x.
    + intros. simpl in *. inversion H. inversion H'. apply empty.
    + intros. simpl in *.
    apply cat_count_rev in H'.
    apply cat_count_rev in H.
    destruct H' as [m1 [m2 [H0 [H1 H8]]]]; subst.
    destruct H as [m3 [m4 [H2 [H3 H8]]]]; subst.
    assert ((m3 + m4 + (m1 + m2)) = (m3 + m1 + (m4 + m2))).
      assert (m4 + (m1 + m2) = m1 + (m4 + m2)).
        rewrite Nat.add_assoc. assert (m4 + m1 = m1 + m4). apply Nat.add_comm.
        rewrite H. rewrite Nat.add_assoc. reflexivity.
        rewrite <- Nat.add_assoc. rewrite H. rewrite Nat.add_assoc. reflexivity.
    rewrite H.
    apply cat_count. apply cat_count. apply H2.
    apply H0.
    apply IHx. apply H1. apply H3.
Qed.

Lemma transpose_lemma2 :
forall T (a:T) x y n f,
count a (zip (buildList y (fun j => (buildList x (fun i => f i j))))) n ->
count a (zip (buildList x (fun i => (buildList y (fun j => f i j))))) n.
Proof.
  induction y.
  - intros. induction x. apply H. apply IHx in H. apply H.
  - simpl in *. intros. apply cat_count_rev in H.
  destruct H as [m [m' [H [H' H2]]]]. subst.
  apply IHy in H'. clear IHy.
  generalize dependent m.
  generalize dependent m'.
  induction x.
    + intros. simpl in *. inversion H. inversion H'. apply empty.
    + intros. simpl in *.
    assert (count a ((f x y :: []) ++ buildList x (fun i : nat => f i y)) m). apply H.
    apply cat_count_rev in H'.
    apply cat_count_rev in H0.
    clear H.
    destruct H' as [m1 [m2 [H0' [H1 H8]]]]; subst.
    destruct H0 as [m3 [m4 [H2 [H3 H8]]]]; subst.
    assert ((m3 + m4 + (m1 + m2)) = (m3 + m1 + (m4 + m2))).
      assert (m4 + (m1 + m2) = m1 + (m4 + m2)).
        rewrite Nat.add_assoc. assert (m4 + m1 = m1 + m4). apply Nat.add_comm.
        rewrite H. rewrite Nat.add_assoc. reflexivity.
        rewrite <- Nat.add_assoc. rewrite H. rewrite Nat.add_assoc. reflexivity.
    rewrite H.
    assert (count a
  ((f x y
   :: []) ++ buildList y (fun j : nat => f x j) ++
      zip (buildList x (fun i : nat => f i y :: buildList y (fun j : nat => f i j))))
  (m3 + m1 + (m4 + m2))).
    rewrite cat_assoc. apply cat_count. apply cat_count. apply H2.
    apply H0'.
    apply IHx. apply H1. apply H3.
    apply H0.
Qed.

Lemma transpose_lemma' :
forall T (a:T) x y z n f,
count a (zip (buildList x (fun i => (zip (buildList y (fun j => zip (buildList z (fun k => f i j k)))))))) n ->
count a (zip (buildList x (fun i => (zip (buildList z (fun k => zip (buildList y (fun j => f i j k)))))))) n.
Proof.
  induction x.
  - intros. simpl in *. induction z. apply H. apply IHz.
  - simpl in *. intros. apply cat_count_rev in H.
  destruct H as [m [m' [H [H' H2]]]]. subst.
  apply IHx in H'. clear IHx.
  apply cat_count.
  apply transpose_lemma. apply H.
  apply H'.
Qed.

Lemma transpose_lemma'2 :
forall T (a:T) x y z n f,
count a (zip (buildList x (fun i => (zip (buildList y (fun j => (buildList z (fun k => f i j k)))))))) n ->
count a (zip (buildList x (fun i => (zip (buildList z (fun k => (buildList y (fun j => f i j k)))))))) n.
Proof.
  induction x.
  - intros. simpl in *. induction z. apply H. apply IHz.
  - simpl in *. intros. apply cat_count_rev in H.
  destruct H as [m [m' [H [H' H2]]]]. subst.
  apply IHx in H'. clear IHx.
  apply cat_count.
  apply transpose_lemma2. apply H.
  apply H'.
Qed.

Lemma transpose_xy_block :
forall (y z x : nat) a b n,
count a (thread_set_3xyz x y z
            (fun x0 : ThreadId_t => x0 :: []) b) n <->
count a (thread_set_3yxz x y z
            (fun x0 : ThreadId_t => x0 :: []) b) n.
Proof.
  intros.
  split; rewrite block_ok_xyz; rewrite block_ok_yxz; apply transpose_lemma; apply H.
Qed.

Lemma transpose_xy_grid :
forall (y z x : nat) a x' y' z' g n,
count a (thread_set_3xyz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n <->
count a (thread_set_3yxz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n.
Proof.
  intros.
  split; rewrite grid_ok_xyz; rewrite grid_ok_yxz; apply transpose_lemma.
Qed.

Lemma transpose_xz_block :
forall (y z x : nat) a b n,
count a (thread_set_3xyz x y z
            (fun x0 : ThreadId_t => x0 :: []) b) n <->
count a (thread_set_3zxy x y z
            (fun x0 : ThreadId_t => x0 :: []) b) n.
Proof.
  intros.
  split; rewrite block_ok_xyz; rewrite block_ok_zxy.
  + intro. apply transpose_lemma. apply transpose_lemma'2. apply H.
  + intro. apply transpose_lemma'2. apply transpose_lemma. apply H.
Qed.

Lemma transpose_xz_grid :
forall (y z x : nat) a x' y' z' g n,
count a (thread_set_3xyz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n <->
count a (thread_set_3zxy x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g) n.
Proof.
  intros.
  split; rewrite grid_ok_xyz; rewrite grid_ok_zxy.
  + intro. apply transpose_lemma. apply transpose_lemma'. apply H.
  + intro. apply transpose_lemma'. apply transpose_lemma. apply H.
Qed.

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

Proposition collection_ok :
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

Proposition collection_ok_physical :
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



Proposition collection_ok_select :
  forall i n v m m' d l r,
(forall (n : nat) (d : dimension) (m m' l r : nat),
    count i (thread_set' (v n)) m ->
    count i (thread_set' (select_range (v n) l r d)) m' -> m' <= m) ->
  count i (zip (buildList n (fun i : nat => thread_set' (v i)))) m
-> count i (zip (buildList n (fun i : nat => thread_set' (select_range (v i) l r d)))) m'
-> m' <= m.
Proof.
  induction n.
  + intros. inversion H1. apply le_0_n.
  + intros. simpl in *.
  apply cat_count_rev in H0.
  apply cat_count_rev in H1.
  destruct H1 as [m1' [m2' [H0' [H1' H2']]]]. subst.
  destruct H0 as [m1 [m2 [H0 [H1 H2]]]]. subst.
  apply H with (m := m1) in H0'.
  apply IHn with (m := m2) (m' := m2') (l := l) (r := r) (d := d) in H.
  apply Nat.add_le_mono. apply H0'. apply H.
  apply H1. apply H1'.
  apply H0.
Qed.

Proposition buildList_end :
  forall T n (f : nat -> T),
  buildList (S n) f = buildList n (fun i => f (S i)) ++ (f 0 :: []).
Proof.
  induction n.
  - reflexivity.
  - intros. simpl. rewrite <- IHn.
  reflexivity.
Qed.

Proposition buildlist_inclusion_right :
  forall T (i:T) n b f m m',
    b <= n -> count i (buildList b f) m' -> count i (buildList n f) m -> m' <= m.
Proof.
  induction n.
  - intros. inversion H. subst. inversion H0; inversion H1; subst. apply le_n.
  - intros. inversion H.
    + subst. assert (m = m'). apply count_unicity with (m := m) in H0. apply H0.
    apply H1. subst; apply le_n.
    + subst. simpl in H1. inversion H1; subst.
      * apply IHn with (f := f) (m := n0) (m' := m') in H0. apply le_S. apply H0. apply H3. apply H7.
      * apply IHn with (f := f) (m := m) (m' := m') in H0. apply H0. apply H3. apply H7.
Qed.

Proposition buildlist_inclusion_left :
  forall T (i:T) n a f m m',
    count i (buildList (n-a) (fun x => f (x+a))) m' -> count i (buildList n f) m -> m' <= m.
Proof.
  induction n.
  - intros. inversion H. subst. inversion H0; inversion H1; subst. apply le_n.
  - intros. destruct a.
      + simpl in *. assert (m = m'). apply count_unicity with (n := m') in H0. apply H0.
        repeat (rewrite Nat.add_0_r in H).
        assert ((fun x => f (x + 0)) = f). apply FunEquality. intro. rewrite Nat.add_0_r. reflexivity.
        rewrite H1 in H. apply H. subst; apply le_n.
      + rewrite buildList_end in H0.
      simpl in *. apply cat_count_rev in H0.
      destruct H0 as [m1 [m2 [H0 [H1 H2]]]]; subst.
      assert ((fun x => f (x + S a)) = (fun x => f (S (x + a)))).
      apply FunEquality. intro. rewrite plus_n_Sm. reflexivity.
      rewrite H2 in H.
      apply IHn with (f := fun i => f (S i)) (m := m1) in H.
      apply Nat.le_trans with (m := m1).
      apply H. apply Nat.le_add_r. apply H0.
Qed.

Proposition buildlist_inclusion :
  forall T (i:T) n a b f m m',
    b <= n -> count i (buildList (b-a) (fun x => f (x+a))) m' -> count i (buildList n f) m -> m' <= m.
Proof.
  intros. assert (exists m, count i (buildList b f) m). apply count_exists.
  destruct H2 as [m'' H2]. apply buildlist_inclusion_left with (m := m'') in H0.
  apply buildlist_inclusion_right with (m := m) (n := n) in H2.
  apply Nat.le_trans with (m := m''). apply H0. apply H2.
  apply H. apply H1. apply H2.
Qed.

Proposition zip_buildlist_inclusion_right :
  forall T (i:T) n b f m m',
    b <= n -> count i (zip (buildList b f)) m' -> count i (zip (buildList n f)) m -> m' <= m.
Proof.
  induction n.
  - intros. inversion H. subst. inversion H0; inversion H1; subst. apply le_n.
  - intros. inversion H.
    + subst. assert (m = m'). apply count_unicity with (m := m) in H0. apply H0.
    apply H1. subst; apply le_n.
    + subst. simpl in H1. apply cat_count_rev in H1.
      destruct H1 as [m1 [m2 [H1 [H2 H5]]]]; subst.
      apply IHn with (f := f) (m := m2) (m' := m') in H0.
      apply Nat.le_trans with (m := m2).
      apply H0. apply Nat.le_add_l. apply H3.
      apply H2.
Qed.

Lemma zip_cat :
  forall T (l1 l2 : List (List T)),
  zip (l1 ++ l2) = zip l1 ++ zip l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite <- cat_assoc. rewrite IHl1. reflexivity.
Qed.

Proposition zip_buildlist_inclusion_left :
  forall T (i:T) n a f m m',
    count i (zip (buildList (n-a) (fun x => f (x+a)))) m' -> count i (zip (buildList n f)) m -> m' <= m.
Proof.
  induction n.
  - intros. inversion H. subst. inversion H0; inversion H1; subst. apply le_n.
  - intros. destruct a.
      + simpl in *. assert (m = m'). apply count_unicity with (n := m') in H0. apply H0.
        assert ((fun x => f (x + 0)) = f). apply FunEquality. intro. rewrite Nat.add_0_r. reflexivity.
        rewrite H1 in H. rewrite Nat.add_0_r in H.
        apply H. subst; apply le_n.
      + rewrite buildList_end in H0.
      simpl in *. rewrite zip_cat in H0. apply cat_count_rev in H0.
      destruct H0 as [m1 [m2 [H0 [H1 H2]]]]; subst.
      assert ((fun x => f (x + S a)) = (fun x => f (S (x + a)))).
      apply FunEquality. intro. rewrite plus_n_Sm. reflexivity.
      rewrite H2 in H.
      apply IHn with (f := fun i => f (S i)) (m := m1) in H.
      apply Nat.le_trans with (m := m1).
      apply H. apply Nat.le_add_r. apply H0.
Qed.

Proposition zip_buildlist_inclusion :
  forall T (i:T) n a b f m m',
    b <= n -> count i (zip (buildList (b-a) (fun x => f (x+a)))) m' -> count i (zip (buildList n f)) m -> m' <= m.
Proof.
  intros. assert (exists m, count i (zip (buildList b f)) m). apply count_exists.
  destruct H2 as [m'' H2]. apply zip_buildlist_inclusion_left with (m := m'') in H0.
  apply zip_buildlist_inclusion_right with (m := m) (n := n) in H2.
  apply Nat.le_trans with (m := m''). apply H0. apply H2.
  apply H. apply H1. apply H2.
Qed.
