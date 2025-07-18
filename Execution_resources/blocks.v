
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
Require Import PeanoNat.

Proposition block_not_contain_larger_on_z :
  forall idx' idy' idz' idx idy idz x y z i j k,
    (i >= x \/ j >= y \/ k >= z) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_1z x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction z.
  - intros. destruct x,y; apply empty.
  - intros.
    destruct H as [H | [H | H]].
    + simpl. destruct x. apply empty. destruct y. apply empty.
    assert (i >= S x \/ j >= S y \/ k >= z). left. apply H.
    apply cons_neq. apply IHz in H0. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
    + simpl. destruct x. apply empty. destruct y. apply empty.
    assert (i >= S x \/ j >= S y \/ k >= z). right. left. apply H.
    apply cons_neq. apply IHz in H0. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
    + simpl. destruct x. apply empty. destruct y. apply empty.
    assert (i >= S x \/ j >= S y \/ k >= z). right. right.
    apply le_S_n. apply le_S. apply H.
    apply cons_neq. apply IHz in H0. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition block_not_contain_larger_on_yz :
  forall idx' idy' idz' idx idy idz x y z i j k,
    (i >= x \/ j >= y \/ k >= z) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_2yz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction y.
  - intros. destruct x; apply empty.
  - intros.
    destruct H as [H | [H | H]].
    + simpl. destruct x. apply empty. destruct z. apply empty.
    assert (i >= S x \/ j >= y \/ k >= S z). left. apply H.
    assert (i >= S x \/ j >= S y \/ k >= z). left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_larger_on_z. apply H1.
    apply IHy in H0. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
    + simpl. destruct x. apply empty. destruct z. apply empty.
    assert (i >= S x \/ j >= y \/ k >= S z). right. left.
      apply le_S_n. apply le_S. apply H.
    assert (i >= S x \/ j >= S y \/ k >= z). right. left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_larger_on_z. apply H1.
    apply IHy in H0. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
    + simpl. destruct x. apply empty. destruct z. apply empty.
    assert (i >= S x \/ j >= y \/ k >= S z). right. right. apply H.
    assert (i >= S x \/ j >= S y \/ k >= z). right. right.
      apply le_S_n. apply le_S. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_larger_on_z. apply H1.
    apply IHy in H0. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition block_not_contain_larger_on_xyz :
  forall idx' idy' idz' idx idy idz x y z i j k,
    i >= x \/ j >= y \/ k >= z ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_3xyz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction x.
  - intros. apply empty.
  - intros.
    destruct H as [H | [H | H]].
    + simpl. destruct y. apply empty. destruct z. apply empty.
    assert (i >= x \/ j >= S y \/ k >= S z). left.
      apply le_S_n. apply le_S. apply H.
    assert (i >= S x \/ j >= y \/ k >= S z). left. apply H.
    assert (i >= S x \/ j >= S y \/ k >= z). left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_larger_on_z. apply H2.
    apply block_not_contain_larger_on_yz. apply H1.
    apply IHx. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
    + simpl. destruct y. apply empty. destruct z. apply empty.
    assert (i >= x \/ j >= S y \/ k >= S z). right. left. apply H.
    assert (i >= S x \/ j >= y \/ k >= S z). right. left.
      apply le_S_n. apply le_S. apply H.
    assert (i >= S x \/ j >= S y \/ k >= z). right. left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_larger_on_z. apply H2.
    apply block_not_contain_larger_on_yz. apply H1.
    apply IHx. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
    + simpl. destruct y. apply empty. destruct z. apply empty.
    assert (i >= x \/ j >= S y \/ k >= S z). right. right. apply H.
    assert (i >= S x \/ j >= y \/ k >= S z). right. right. apply H.
    assert (i >= S x \/ j >= S y \/ k >= z). right. right.
      apply le_S_n. apply le_S. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_larger_on_z. apply H2.
    apply block_not_contain_larger_on_yz. apply H1.
    apply IHx. apply H0.
    intro C. inversion C; subst. apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition block_not_contain_smaller_on_z :
  forall idx idy idz x y z i j k,
    (S i < x \/ S j < y) ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_1z x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction z.
  - intros. destruct x,y; apply empty.
  - intros.
    destruct H as [H | H].
    + destruct x. inversion H.
      destruct y. apply empty.
      simpl.
      apply cons_neq.
      assert (S i < S x \/ S j < S y). left. apply H.
      apply IHz with (k := k) in H0. apply H0.
      intro C. inversion C. subst.
      apply Nat.lt_irrefl in H. apply H.
    + destruct y. inversion H.
      destruct x. apply empty.
      simpl.
      apply cons_neq.
      assert (S i < S x \/ S j < S y). right. apply H.
      apply IHz with (k := k) in H0. apply H0.
      intro C. inversion C. subst.
      apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition block_not_contain_smaller_on_yz :
  forall idx idy idz x y z i j k,
    S i < x ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_2yz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction y.
  - intros. destruct x,z; apply empty.
  - intros.
    destruct x. inversion H.
    destruct z. apply empty.
    simpl.
    apply cons_neq.
    apply cat_count with (m := 0) (n := 0).
    apply block_not_contain_smaller_on_z. left. apply H.
    apply IHy with (k := k) (j := j) (z := (S z)) in H. apply H.
    intro C. inversion C. subst.
    apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition block_contain_smaller_on_z :
  forall idx idy idz x y z i j k,
    S i = x -> S j = y -> k < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_1z x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 1.
Proof.
  induction z.
  - intros. inversion H1.
  - intros.
    destruct x. inversion H.
    destruct y. inversion H0.
    simpl.
    inversion H; inversion H0; subst.
    inversion H1.
    + subst.
      apply cons_eq.
      apply block_not_contain_larger_on_z.
      right. right. apply le_n.
    + subst.
      apply cons_neq.
      apply IHz with (j := y) (k := k) in H.
      apply H.
      reflexivity.
      apply H3.
      intro C. inversion C. subst.
      apply Nat.lt_irrefl in H3. apply H3.
Qed.

Proposition block_contain_smaller_on_yz :
  forall idx idy idz x y z i j k,
    S i = x -> j < y -> k < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_2yz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 1.
Proof.
  induction y.
  - intros. inversion H0.
  - intros.
    destruct x. inversion H.
    destruct z. inversion H1.
    simpl.
    inversion H; subst.
    inversion H0.
    + subst.
      inversion H1.
      * subst.
        apply cons_eq.
        apply cat_count with (n := 0) (m := 0).
        apply block_not_contain_larger_on_z. right. right. apply le_n.
        apply block_not_contain_larger_on_yz. right. left. apply le_n.
      * apply cons_neq.
        subst.
        apply cat_count with (m := 1) (n := 0).
        apply block_contain_smaller_on_z.
        reflexivity. reflexivity. apply H3.
        apply block_not_contain_larger_on_yz.
        right. left. apply le_n.
        intro C; inversion C; subst.
        apply Nat.lt_irrefl in H3. apply H3.
    + subst.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 1).
      apply block_not_contain_smaller_on_z.
      right. apply le_n_S. apply H3.
      apply IHy with (j := j) (k := k) (z := (S z)) in H.
      apply H.
      apply H3.
      apply H1.
      intro C; inversion C; subst.
      apply Nat.lt_irrefl in H3. apply H3.
Qed.

Proposition block_contain_smaller_on_xyz :
  forall idx idy idz x y z i j k,
    i < x -> j < y -> k < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_3xyz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 1.
Proof.
  induction x.
  - intros. inversion H.
  - intros.
    destruct y. inversion H0.
    destruct z. inversion H1.
    simpl.
    inversion H.
    + subst.
      inversion H0.
      * subst.
        inversion H1.
        --  subst.
            apply cons_eq.
            apply cat_count with (n := 0) (m := 0).
            apply cat_count with (n := 0) (m := 0).
            apply block_not_contain_larger_on_z. right. right. apply le_n.
            apply block_not_contain_larger_on_yz. right. left. apply le_n.
            apply block_not_contain_larger_on_xyz. left. apply le_n.
        -- apply cons_neq.
            subst.
            apply cat_count with (m := 1) (n := 0).
            apply cat_count with (m := 1) (n := 0).
            apply block_contain_smaller_on_z.
            reflexivity. reflexivity. apply H3.
            apply block_not_contain_larger_on_yz. right. left. apply le_n.
            apply block_not_contain_larger_on_xyz. left. apply le_n.
            intro C; inversion C; subst.
            apply Nat.lt_irrefl in H3. apply H3.
      * subst.
        apply cons_neq.
        apply cat_count with (m := 1) (n := 0).
        apply cat_count with (m := 0) (n := 1).
        apply block_not_contain_smaller_on_z.
        right. apply le_n_S. apply H3.
        apply block_contain_smaller_on_yz.
        reflexivity. apply H3. apply H1.
        apply block_not_contain_larger_on_xyz. left. apply le_n.
        intro C; inversion C; subst.
        apply Nat.lt_irrefl in H3. apply H3.
  + subst.
    apply cons_neq.
    apply cat_count with (m := 0) (n := 1).
    apply cat_count with (m := 0) (n := 0).
    apply block_not_contain_smaller_on_z.
    left. apply le_n_S. apply H3.
    apply block_not_contain_smaller_on_yz.
    apply le_n_S. apply H3.
    apply IHx with (j := j) (k := k) (y := (S y)) (z := (S z)) in H3.
    apply H3.
    apply H0.
    apply H1.
    intro C; inversion C; subst.
    apply Nat.lt_irrefl in H3. apply H3.
Qed.

Proposition block_not_contain_other_indices_on_z :
  forall idx' idy' idz' idx idy idz x y z i j k,
    (idx' <> idx \/ idy' <> idy \/ idz' <> idz) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_1z x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction z.
  - intros. destruct x,y; apply empty.
  - intros.
    destruct H as [H | [H | H]].
    + simpl. destruct x. apply empty. destruct y. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). left. apply H.
    apply cons_neq. apply IHz with (i := i) (j := j) (k := k) in H0. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
    + simpl. destruct x. apply empty. destruct y. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). right. left. apply H.
    apply cons_neq. apply IHz with (i := i) (j := j) (k := k) in H0. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
    + simpl. destruct x. apply empty. destruct y. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). right. right.
    apply H.
    apply cons_neq. apply IHz with (i := i) (j := j) (k := k) in H0. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
Qed.

Proposition block_not_contain_other_indices_on_yz :
  forall idx' idy' idz' idx idy idz x y z i j k,
    (idx' <> idx \/ idy' <> idy \/ idz' <> idz) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_2yz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction y.
  - intros. destruct x; apply empty.
  - intros.
    destruct H as [H | [H | H]].
    + simpl. destruct x. apply empty. destruct z. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_other_indices_on_z. apply H0.
    apply IHy with (i := i) (j := j) (k := k) (z := S z) in H0. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
    + simpl. destruct x. apply empty. destruct z. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). right. left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_other_indices_on_z. apply H0.
    apply IHy with (i := i) (j := j) (k := k) (z := S z) in H0. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
    + simpl. destruct x. apply empty. destruct z. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). right. right. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_other_indices_on_z. apply H0.
    apply IHy with (i := i) (j := j) (k := k) (z := S z) in H0. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
Qed.

Proposition block_not_contain_other_indices_on_xyz :
  forall idx' idy' idz' idx idy idz x y z i j k,
    (idx' <> idx \/ idy' <> idy \/ idz' <> idz) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_3xyz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  induction x.
  - intros. apply empty.
  - intros.
    destruct H as [H | [H | H]].
    + simpl. destruct y. apply empty. destruct z. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_other_indices_on_z. apply H0.
    apply block_not_contain_other_indices_on_yz. apply H0.
    apply IHx. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
    + simpl. destruct y. apply empty. destruct z. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). right. left. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_other_indices_on_z. apply H0.
    apply block_not_contain_other_indices_on_yz. apply H0.
    apply IHx. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
    + simpl. destruct y. apply empty. destruct z. apply empty.
    assert (idx' <> idx \/ idy' <> idy \/ idz' <> idz). right. right. apply H.
    apply cons_neq.
    apply cat_count with (n := 0) (m := 0).
    apply cat_count with (n := 0) (m := 0).
    apply block_not_contain_other_indices_on_z. apply H0.
    apply block_not_contain_other_indices_on_yz. apply H0.
    apply IHx. apply H0.
    intro C. inversion C; subst. apply H. reflexivity.
Qed.

Proposition empty_z :
  forall (z x y x' y' z' : nat) fx fy fz fx' fy' fz',
    thread_set_1z x y z (fun b => []) (fun (i j k i0 j0 k0 : nat) => (((fx' i x, fy' j y, fz' k z),(fx i0 x',fy j0 y', fz k0 z')) : ThreadId_t)) = [].
Proof.
  induction z.
  - destruct x,y; reflexivity.
  - intros. simpl. destruct x,y; try reflexivity.
  simpl. apply IHz with (fz' := fun i x => fz' i (S x)).
Qed.

Proposition empty_yz :
  forall (z x y x' y' z' : nat) fx fy fz fx' fy' fz',
    thread_set_2yz x y z (fun b => []) (fun (i j k i0 j0 k0 : nat) => (((fx' i x, fy' j y, fz' k z),(fx i0 x',fy j0 y', fz k0 z')) : ThreadId_t)) = [].
Proof.
  induction y.
  - destruct x,z; reflexivity.
  - intros. simpl. destruct x,z; try reflexivity.
  simpl.
  assert (thread_set_1z (S x) (S y) z (fun _ : nat -> nat -> nat -> ThreadId_t => [])
          (fun i j k i0 j0 k0 : nat =>
          (fx' i (S x), fy' j (S y), fz' k (S z), (fx i0 x', fy j0 y', fz k0 z'))) = []).
    apply empty_z with (fz' := fun i x => fz' i (S x)).
  rewrite H; clear H. simpl.
  apply IHy with (fy' := fun i x => fy' i (S x)).
Qed.

Proposition empty_xyz :
  forall (z x y x' y' z' : nat) fx fy fz fx' fy' fz',
    thread_set_3xyz x y z (fun b => []) (fun (i j k i0 j0 k0 : nat) => (((fx' i x, fy' j y, fz' k z),(fx i0 x',fy j0 y', fz k0 z')) : ThreadId_t)) = [].
Proof.
  induction x.
  - destruct y,z; reflexivity.
  - intros. simpl. destruct y,z; try reflexivity.
  simpl.
  assert (thread_set_1z (S x) (S y) z (fun _ : nat -> nat -> nat -> ThreadId_t => [])
          (fun i j k i0 j0 k0 : nat =>
          (fx' i (S x), fy' j (S y), fz' k (S z), (fx i0 x', fy j0 y', fz k0 z'))) = []).
    apply empty_z with (fz' := fun i x => fz' i (S x)).
  rewrite H; clear H.
  assert (thread_set_2yz (S x) y (S z) (fun _ : nat -> nat -> nat -> ThreadId_t => [])
          (fun i j k i0 j0 k0 : nat =>
          (fx' i (S x), fy' j (S y), fz' k (S z), (fx i0 x', fy j0 y', fz k0 z'))) = []).
    apply empty_yz with (fy' := fun i x => fy' i (S x)).
  rewrite H; clear H. simpl.
  apply IHx with (fx' := fun i x => fx' i (S x)).
Qed.

Proposition empty_grid_z :
  forall (z x y x' y' z' : nat),
    (x' = 0 \/ y' = 0 \/ z' = 0) ->
    (thread_set_1z x y z (fun b => []) (build_grid (x,y,z) (x',y',z'))) = [].
Proof.
  intros.
  simpl.
  destruct x',y',z'; simpl;
  try (apply empty_z with (x := x) (y := y) (z := z)
        (x' := 0) (y' := 0) (z' := 0)
        (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
        (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i)).
Qed.

Proposition empty_grid_yz :
  forall (z x y x' y' z' : nat),
    (x' = 0 \/ y' = 0 \/ z' = 0) ->
    (thread_set_2yz x y z (fun b => []) (build_grid (x,y,z) (x',y',z'))) = [].
Proof.
  intros.
  simpl.
  destruct x',y',z'; simpl;
  try (apply empty_yz with (x := x) (y := y) (z := z)
        (x' := 0) (y' := 0) (z' := 0)
        (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
        (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i)).
Qed.

Proposition empty_grid_xyz :
  forall (z x y x' y' z' : nat),
    (thread_set_3xyz x y z (fun b => []) (build_grid (x,y,z) (x',y',z'))) = [].
Proof.
  intros.
  simpl.
  destruct x',y',z'; simpl;
  try (apply empty_xyz with (x := x) (y := y) (z := z)
        (x' := 0) (y' := 0) (z' := 0)
        (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
        (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i)).
Qed.

Lemma cons_cat :
  forall T (x:T) l,
    x::l = (x :: [])++l.
Proof.
  reflexivity.
Qed.


Proposition block_correct_z :
  forall idx idy idz idx' idy' idz' x y z i j k,
    ((i >= x \/ j >= y \/ k >= z) \/ (idx' <> idx \/ idy' <> idy \/ idz' <> idz)) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_1z x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  intros.
  destruct H as [H | H].
  apply block_not_contain_larger_on_z. apply H.
  apply block_not_contain_other_indices_on_z. apply H.
Qed.

Proposition block_correct_yz :
  forall idx idy idz idx' idy' idz' x y z i j k,
    ((i >= x \/ j >= y \/ k >= z) \/ (idx' <> idx \/ idy' <> idy \/ idz' <> idz)) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set_2yz x y z (fun x => x :: []) (build_block (x,y,z) (idx,idy,idz))) 0.
Proof.
  intros.
  destruct H as [H | H].
  apply block_not_contain_larger_on_yz. apply H.
  apply block_not_contain_other_indices_on_yz. apply H.
Qed.

Proposition block_correct :
  forall idx idy idz idx' idy' idz' x y z i j k,
    ((i >= x \/ j >= y \/ k >= z) \/ (idx' <> idx \/ idy' <> idy \/ idz' <> idz)) ->
    count ((idx',idy',idz'),(i,j,k)) (thread_set' (Block' (x,y,z) (idx,idy,idz))) 0.
Proof.
  intros.
  destruct H as [H | H].
  apply block_not_contain_larger_on_xyz. apply H.
  apply block_not_contain_other_indices_on_xyz. apply H.
Qed.

Proposition block_complete :
  forall idx idy idz x y z i j k,
    i < x -> j < y -> k < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set' (Block' (x,y,z) (idx,idy,idz))) 1.
Proof.
  apply block_contain_smaller_on_xyz.
Qed.
