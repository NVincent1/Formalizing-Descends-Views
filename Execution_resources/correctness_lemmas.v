
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Axiom FunEquality :
  forall T T' (f g : T -> T'),
  f = g <-> forall x, (f x) = (g x).

(** `forall n, count x l1 n -> count x l2 n` implies that l1 and l2 has the same elements the same amount of time *)

Proposition count_impl_equiv :
  forall T (x : T) l1 l2,
  (forall n, count x l1 n -> count x l2 n) ->
  forall n, count x l2 n -> count x l1 n.
Proof.
  intros. assert (exists m, count x l1 m). apply count_exists.
  destruct H1. apply H in H1 as H2. apply count_unicity with (m := x0) in H0. subst. apply H1.
  apply H2.
Qed.

(** Transpositions (changing the order in which we consider the dimensions) *)

Lemma transpose_lemma_xy_zip :
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

Lemma transpose_lemma_xy :
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

Lemma transpose_lemma_yz_zip :
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
  apply transpose_lemma_xy_zip. apply H.
  apply H'.
Qed.

Lemma transpose_lemma_yz :
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
  apply transpose_lemma_xy. apply H.
  apply H'.
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

(** Subselection of a list gives a subset of the original elements *)

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

(** `next_multiple n m` outputs the smallest multiple of m that is larger or equal to n *)

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

Lemma next_multiple_0_m :
  forall m,
  next_multiple 0 m = 0.
Proof.
  intros.
  unfold next_multiple. rewrite Nat.Div0.mod_0_l. reflexivity.
Qed.

Lemma next_multiple_n_1 :
  forall n,
  next_multiple n 1 = n.
Proof.
  intros.
  assert (next_multiple n 1 = next_multiple (n*1) 1).
    rewrite Nat.mul_1_r. reflexivity.
  rewrite H. rewrite next_multiple_unchange_multiple.
  rewrite Nat.mul_1_r. reflexivity.
Qed.

Lemma next_multiple_lt_0 :
  forall n m, n > 0 -> m <> 0 -> next_multiple n m > 0.
Proof.
  intros.
  destruct n,m.
  + inversion H.
  + inversion H.
  + exfalso. apply H0. reflexivity.
  + rewrite Nat.Div0.div_mod with (a := S n) (b := S m).
  destruct (S n mod S m) eqn : E.
    * rewrite Nat.add_0_r. rewrite Nat.mul_comm. rewrite next_multiple_unchange_multiple.
      assert (S n >= S m). apply Nat.Div0.mod_divides in E. destruct E.
      destruct x. rewrite Nat.mul_0_r in H1. rewrite H1 in H. inversion H.
      rewrite H1. rewrite <- Nat.mul_1_r. apply Nat.mul_le_mono_l.
      apply le_n_S. apply le_0_n. rewrite Nat.mul_comm.
      apply Nat.Div0.div_exact in E. rewrite <- E. apply Nat.lt_0_succ.
    * rewrite Nat.mul_comm. rewrite next_multiple_is_a_multiple.
      rewrite <- Nat.mul_0_r with (n := 0). apply Nat.mul_lt_mono.
      apply Nat.lt_0_succ. apply Nat.lt_0_succ.
      rewrite <- E. apply Nat.mod_upper_bound. apply H0. apply Nat.lt_0_succ.
Qed.

(** euclidian division *)

Lemma mod_decomposition :
  forall m n,
  exists k, n = k*m + (n mod m)
.
Proof.
  intros.
  exists (n/m).
  rewrite Nat.mul_comm. apply Nat.Div0.div_mod.
Qed.

(** Splitting the element count of a block on x dimension *)

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
    repeat (rewrite thread_set_1z_correct_on_block in *).
    repeat (rewrite thread_set_2yz_correct_on_block in *).
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

(** For f injective, `map f` preserves the occurences of elements in the list it is applied to *)

Proposition map_injection :
  forall T T' l1 (f : T -> T'), (forall x y, f x = f y -> x = y) ->
    (forall a n, count a l1 n -> count (f a) (map f l1) n).
Proof.
  induction l1.
  - intros. inversion H0 ; subst. apply empty.
  - intros. simpl. inversion H0; subst.
      apply cons_eq. apply IHl1. apply H. apply H5.
      apply cons_neq. apply IHl1. apply H. apply H5. intro. apply H in H1. apply Hneq. apply H1.
Qed.

(** Inductive steps for correctness proofs of for_all and select *)

Proposition induction_step_collection_select :
  forall i n v m m' d l r,
(forall n' n0 n0', n' < n -> count i (logical_thread_set (v n')) n0 ->
    count i (logical_thread_set (sub_selection (v n') l r d)) n0' -> n0' <= n0) ->
  count i (zip (buildList n (fun i : nat => logical_thread_set (v i)))) m
-> count i (zip (buildList n (fun i0 : nat => logical_thread_set (sub_selection (v i0) l r d)))) m'
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
    count i (logical_thread_set (v n')) n0 ->
    count i (logical_thread_set (sub_selection (v n') l r d)) n0' -> n0' <= n0).
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
    count i (physical_thread_set (sub_selection (v n') l r d) f) n0' -> n0' <= n0) ->
  count i (zip (buildList n (fun i : nat => physical_thread_set (v i) f))) m
-> count i (zip (buildList n (fun i0 : nat => physical_thread_set (sub_selection (v i0) l r d) f))) m'
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
    count i (physical_thread_set (sub_selection (v n') l r d) f) n0' -> n0' <= n0).
    intros. apply le_S in H2. apply H with (n0 := n0) (n0' := n0')in H2.
    apply H2. apply H3. apply H4.
  apply H with (n0 := m1) in H0'.
  apply IHn with (m := m2) (m' := m2') (l := l) (r := r) (d := d) in H2.
  apply Nat.add_le_mono. apply H0'. apply H2.
  apply H1. apply H1'.
  apply le_n. apply H0.
Qed.

Proposition induction_step_collection_forall :
  forall i n v n0 d,
(forall n' n0, n' < n -> count i (logical_thread_set (v n')) n0 ->
    count i (logical_thread_set (for_all (v n') d)) n0) ->
  count i (zip (buildList n (fun i : nat => logical_thread_set (v i)))) n0
-> count i (zip (buildList n (fun i0 : nat => logical_thread_set (for_all (v i0) d))))
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

