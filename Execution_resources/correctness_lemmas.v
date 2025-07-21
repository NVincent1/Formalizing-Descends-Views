
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

(** Rewriting thread_set with buildList *)
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

(** Transpositions (changing the order in which we consider the dimensions) *)

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

Lemma next_multiple_unchange_multiple :
  forall n m,
  next_multiple (n*m) m = n*m.
Proof.
  destruct n.
  - intro. simpl. unfold next_multiple. rewrite Nat.Div0.mod_0_l. reflexivity.
  - destruct m. rewrite Nat.mul_0_r. reflexivity.
    unfold next_multiple. rewrite Nat.Div0.mod_mul. reflexivity.
Qed.

Lemma next_multiple_aux_is_a_multiple :
  forall n k m,
    k < m ->
  next_multiple_aux (n*m+k) m = n*m.
Proof.
  destruct n.
  - intros. simpl. unfold next_multiple_aux.
    induction k.
    + reflexivity.
    + assert (S k mod m = S k). apply Nat.mod_small. apply H.
    rewrite H0. apply IHk. apply le_S_n. apply le_S. apply H.
  - destruct m; intros. rewrite Nat.mul_0_r. inversion H.
    induction k.
    + assert ((S n * S m + 0) mod (S m) = 0). rewrite Nat.Div0.add_mod. rewrite Nat.Div0.mod_mul.
      rewrite Nat.mod_small. rewrite Nat.mod_small. reflexivity. apply H.  rewrite Nat.mod_small; apply H.
      simpl in *. rewrite H0. rewrite Nat.add_0_r. reflexivity.
    + assert ((S n * S m + S k) mod (S m) = S k). rewrite Nat.Div0.add_mod. rewrite Nat.Div0.mod_mul.
      rewrite Nat.mod_small. rewrite Nat.mod_small. reflexivity. apply H.  rewrite Nat.mod_small; apply H.
      simpl in H0. simpl. rewrite H0.
      clear H0.
      assert (m + n * S m + S k = S n * S m + k).
        simpl. rewrite plus_n_Sm. reflexivity.
      rewrite H0. apply IHk. apply le_S. apply le_S_n. apply H.
Qed.

Lemma next_multiple_is_a_multiple :
  forall n k m,
    k < m -> k > 0 ->
  next_multiple (n*m+k) m = (S n)*m.
Proof.
  destruct k.
  - intros. inversion H0.
  - intros. unfold next_multiple.
  assert ((n * m + S k) mod m = S k). rewrite Nat.Div0.add_mod. rewrite Nat.Div0.mod_mul.
    rewrite Nat.mod_small. rewrite Nat.mod_small. reflexivity. apply H.  rewrite Nat.mod_small; apply H.
    rewrite H1. assert (n * m + S k + m = (S n) * m + S k). simpl. rewrite Nat.add_comm.
    rewrite Nat.add_assoc. reflexivity. rewrite H2.
    apply next_multiple_aux_is_a_multiple. apply H.
Qed.

Lemma mod_decomposition :
  forall m n,
  exists k, n = k*m + (n mod m)
.
Proof.
  intros.
  exists (n/m).
  rewrite Nat.mul_comm. apply Nat.Div0.div_mod.
Qed.

Lemma next_multiple_0 :
  forall m,
  next_multiple 0 m = 0.
Proof.
  intros.
  unfold next_multiple. rewrite Nat.Div0.mod_0_l. reflexivity.
Qed.

Lemma next_multiple_1 :
  forall n,
  next_multiple n 1 = n.
Proof.
  intros.
  assert (next_multiple n 1 = next_multiple (n*1) 1).
    rewrite Nat.mul_1_r. reflexivity.
  rewrite H. rewrite next_multiple_unchange_multiple.
  rewrite Nat.mul_1_r. reflexivity.
Qed.

Proposition expand_block :
  forall T (i : T) x dx y z n n' f b,
  count i (map f (thread_set_3xyz dx y z (fun x0 : ThreadId_t => x0 :: [])
        (fun i0 j k0 : nat => b (x+i0) j k0))) n /\ 
        count i (map f (thread_set_3xyz x y z (fun x0 : ThreadId_t => x0 :: [])
        (fun i0 j k0 : nat => b i0 j k0))) n' ->
        count i (map f (thread_set_3xyz (x+dx) y z (fun x0 : ThreadId_t => x0 :: [])
        (fun i0 j k0 : nat => b i0 j k0))) (n + n').
Proof.
  induction dx.
  - intros. simpl in *. destruct H; inversion H;subst. rewrite Nat.add_0_r. apply H0.
  - simpl in *. destruct y,z.
    + intros. destruct H. destruct x; inversion H; inversion H0; subst; apply empty.
    + intros. destruct H. destruct x; inversion H; inversion H0; subst; apply empty.
    + intros. destruct H. destruct x; inversion H; inversion H0; subst; apply empty.
    + intros. destruct H. rewrite cons_cat in H.
    repeat (rewrite map_cat in *).
    apply cat_count_rev in H.
    destruct H as [m1 [m2 [H1 [H2 H']]]]; subst.
    apply cat_count_rev in H2.
    destruct H2 as [m3 [m4 [H2 [H4 H']]]]; subst.
    apply cat_count_rev in H2.
    destruct H2 as [m5 [m6 [H2 [H3 H']]]]; subst.
    rewrite <- plus_n_Sm. simpl.
    repeat (rewrite block_ok_z in *).
    repeat (rewrite block_ok_yz in *).
    rewrite cons_cat.
    assert (m1 + (m5 + m6 + m4) + n' = m1 + ((m5 + m6) + (m4 + n'))). {
      clear.
      rewrite Nat.add_comm.
      repeat (rewrite Nat.add_assoc).
      assert (m4 + n' = n' + m4). apply Nat.add_comm.
      assert (n' + m1 + m5 + m6 + m4 = n' + (m1 + m5 + m6 + m4)). repeat (rewrite Nat.add_assoc). reflexivity.
      rewrite H0. rewrite Nat.add_comm. rewrite <- Nat.add_assoc. rewrite H. reflexivity.
    } rewrite H. clear H.
    repeat (rewrite map_cat).
    apply cat_count. apply H1.
    apply cat_count.
    apply cat_count. apply H2. apply H3.
    apply IHdx. split. apply H4. apply H0.
Qed.

Fixpoint sz {T : Type} (l : List T) :=
  match l with
  | [] => 0
  | h::tl => S (sz tl)
end.

Inductive contains {T : Type} : T -> List T -> Prop :=
  | contains_eq (x : T) (l : List T) : contains x (x::l)
  | contains_cons (x : T) (h : T) (l : List T) (Hcons : contains x l) : contains x (h::l)
.

Proposition contains_count :
  forall T (x : T) l,
    contains x l <-> (forall n, count x l n -> n > 0).
Proof.
  induction l.
  - split; intros. inversion H. assert (count x [] 0). apply empty. apply H in H0. inversion H0.
  - split; intros.
    * inversion H; subst.
      + inversion H0; subst. apply le_n_S. apply le_0_n. exfalso. apply Hneq. reflexivity.
      + inversion H0; subst. apply le_n_S. apply le_0_n.
        apply IHl with (n := n) in Hcons. apply Hcons. apply H5.
    * assert (x = h \/ x <> h). apply excluded_middle.
      destruct H0. subst. apply contains_eq. apply contains_cons. apply IHl.
      intros. apply cons_neq with (y := h) in H1.
      apply H in H1. apply H1. apply H0.
Qed.

Proposition contains_reorder :
  forall T (y : T) l,
  contains y l -> exists l2, (forall x n, count x l n <-> count x (y::l2) n).
Proof.
  induction l.
  - intros. inversion H.
  - intros. inversion H; subst.
    + exists l. split;intros; apply H0.
    + apply IHl in Hcons as Hex.
    destruct Hex as [l' Hex]. exists (h :: l').
    intros. split;intros.
    -- rewrite cons_cat. rewrite count_reorder.
    simpl. inversion H0; subst.
      * apply cons_eq. apply Hex. apply H5.
      * apply cons_neq. apply Hex. apply H5. apply Hneq.
    -- rewrite cons_cat in H0. rewrite count_reorder in H0.
    simpl. inversion H0; subst.
      * apply cons_eq. apply Hex. apply H5.
      * apply cons_neq. apply Hex. apply H5. apply Hneq.
Qed.

Proposition contains_reorder_map :
  forall T T' y (f : T -> T') l,
  contains (f y) (map f l) -> contains y l -> exists l2, (forall x n, count (f x) (map f l) n <-> count (f x) (map f (y::l2)) n) /\ (forall x n, count x l n <-> count x (y::l2) n).
Proof.
  induction l.
  - intros. inversion H.
  - intros. inversion H0; subst.
    + exists l. split;split;intro;apply H1.
    + apply IHl in Hcons as Hex.
    destruct Hex as [l' Hex]. exists (h :: l').
    intros. split;split;intros.
    -- simpl. rewrite cons_cat. rewrite count_reorder.
    simpl. inversion H1; subst.
      * apply cons_eq. apply Hex. apply H6.
      * apply cons_neq. apply Hex. apply H6. apply Hneq.
    -- simpl in H1. rewrite cons_cat in H1. rewrite count_reorder in H1.
    simpl. inversion H1; subst.
      * apply cons_eq. apply Hex. apply H6.
      * apply cons_neq. apply Hex. apply H6. apply Hneq.
    -- simpl. rewrite cons_cat. rewrite count_reorder.
    simpl. inversion H1; subst.
      * apply cons_eq. apply Hex. apply H6.
      * apply cons_neq. apply Hex. apply H6. apply Hneq.
    -- simpl in H1. rewrite cons_cat in H1. rewrite count_reorder in H1.
    simpl. inversion H1; subst.
      * apply cons_eq. apply Hex. apply H6.
      * apply cons_neq. apply Hex. apply H6. apply Hneq.
    -- clear H0. clear H. clear IHl. induction l.
      * inversion Hcons.
      * simpl. inversion Hcons. apply contains_eq.
        apply contains_cons. apply IHl. apply Hcons0.
Qed.

Lemma contains_map :
  forall T T' x l (f : T -> T'),
  contains x l -> contains (f x) (map f l).
Proof.
  induction l.
  - intros. inversion H.
  - intros. simpl. inversion H. apply contains_eq.
    subst. apply contains_cons. apply IHl. apply Hcons.
Qed.

Proposition map_injection_aux :
  forall T T' n l1 l2 (f : T -> T'), sz l1 = n ->
    (forall a n, count a l1 n -> count a l2 n) ->
    (forall a n, count (f a) (map f l1) n -> count (f a) (map f l2) n).
Proof.
  induction n;destruct l1;destruct l2;intros;try (inversion H).
  - apply H1.
  - assert (count h [] 0). apply empty.
  apply H0 in H2. inversion H2; subst. exfalso. apply Hneq. reflexivity.
  - assert (count h [] 0). apply empty.
  apply count_impl_equiv with (l1 := (h :: l1)) in H2. inversion H2; subst.
  exfalso. apply Hneq. reflexivity.
  apply H0.
  - assert (contains h (h0 :: l2)).
    apply contains_count. intros.
    assert (exists n, count h (h :: l1) (S n)).
      assert (exists m, count h (l1) m). apply count_exists. destruct H4. apply cons_eq in H4.
      exists x. apply H4.
    destruct H4 as [m H4].
    apply H0 in H4. apply count_unicity with (m := n1) in H4.
    subst. apply le_n_S. apply le_0_n. apply H2.
    apply contains_map with (f := f) in H2 as H4.
    apply contains_reorder_map with (f := f) in H2. destruct H2 as [l2' [H2 H2']].
    apply H2. simpl in *.
    inversion H1.
      + apply IHn with (l2 := l2') (f := f) (a := a) (n := n1) in H3.
        apply cons_eq. apply H3.
        intros. subst. assert (exists m, count a0 (h::l1) m). apply count_exists.
        destruct H3 as [m H3].
        inversion H3; subst; apply H0 in H3; apply H2' in H3; apply count_unicity with (m := n2) in H12;subst;
          inversion H3;subst.
        * apply H11.
        * exfalso. apply Hneq. reflexivity.
        * apply H10.
        * exfalso. apply Hneq. reflexivity.
        * exfalso. apply Hneq. reflexivity.
        * apply H12.
        * exfalso. apply Hneq. reflexivity.
        * apply H10.
        * apply H9.
      + apply IHn with (l2 := l2') (f := f) (a := a) (n := n0) in H3.
        apply cons_neq. apply H3. apply Hneq.
        intros. subst. assert (exists m, count a0 (h::l1) m). apply count_exists.
        destruct H3 as [m H3].
        inversion H3; subst; apply H0 in H3; apply H2' in H3; apply count_unicity with (m := n2) in H11;subst;
          inversion H3;subst.
        * assumption.
        * exfalso. apply Hneq0. reflexivity.
        * assumption.
        * exfalso. apply Hneq0. reflexivity.
        * exfalso. apply Hneq0. reflexivity.
        * assumption.
        * exfalso. apply Hneq0. reflexivity.
        * assumption.
        * assumption.
      + apply H4.
Qed.

Proposition map_injection :
  forall T T' l1 l2 (f : T -> T'),
    (forall a n, count a l1 n -> count a l2 n) ->
    (forall a n, count (f a) (map f l1) n -> count (f a) (map f l2) n).
Proof.
  intros. apply map_injection_aux with (l1 := l1) (n := sz l1).
  reflexivity. apply H. apply H0.
Qed.
