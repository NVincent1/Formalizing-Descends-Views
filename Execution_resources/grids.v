
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import blocks.
From Views.Execution_resources Require Import correctness_lemmas.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.

Proposition grid_not_contain_larger_on_z :
  forall z x y x' y' z' idx idy idz i j k,
    ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= y \/ idz >= z)) ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_1z x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (build_grid (x,y,z) (x', y', z'))) 0.
Proof.
  induction z.
  - intros. destruct x,y; apply empty.
  - intros x y x' y' z' idx idy idz i j k H.
    destruct H as [H | H].
    + destruct H as [H | [H | H]].
      * simpl. destruct x. apply empty. destruct y. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= S y \/ idz >= z)). left. left. apply H.
      destruct x',y',z'; try (simpl;
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i); apply empty).
      simpl.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. left. apply H.
      apply block_correct_yz.
      left. left. apply H.
      apply block_correct.
      left. left. apply le_S_n. apply le_S. apply H.
      simpl in IHz.
      apply IHz with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct y. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= S y \/ idz >= z)). left. right. left. apply H.
      destruct x',y',z'; try (simpl;
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i); apply empty).
      simpl.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. right. left. apply H.
      apply block_correct_yz.
      left. right. left. apply le_S_n. apply le_S. apply H.
      apply block_correct.
      left. right. left. apply H.
      simpl in IHz.
      apply IHz with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct y. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= S y \/ idz >= z)). left. right. right. apply H.
      destruct x',y',z'; try (simpl;
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i); apply empty).
      simpl.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. right. right. apply le_S_n. apply le_S. apply H.
      apply block_correct_yz.
      left. right. right. apply H.
      apply block_correct.
      left. right. right. apply H.
      simpl in IHz.
      apply IHz with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
    + destruct H as [H | [H | H]].
      * simpl. destruct x. apply empty. destruct y. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= S y \/ idz >= z)). right. left. apply H.
      destruct x',y',z'; try (simpl;
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i); apply empty).
      simpl.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply IHz with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct y. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= S y \/ idz >= z)). right. right. left. apply H.
      destruct x',y',z'; try (simpl;
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i); apply empty).
      simpl.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply IHz with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct y. apply empty.
      assert (H' : idz >= z).
      apply le_S_n. apply le_S. apply H.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= S y \/ idz >= z)). right. right. right. apply H'.
      destruct x',y',z'; try (simpl;
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i); apply empty).
      simpl.
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply IHz with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition grid_not_contain_larger_on_yz :
  forall y z x x' y' z' idx idy idz i j k,
    ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= y \/ idz >= z)) ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_2yz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (build_grid (x,y,z) (x', y', z'))) 0.
Proof.
  induction y.
  - intros. destruct x,z; apply empty.
  - intros z x x' y' z' idx idy idz i j k H.
    destruct H as [H | H].
    + destruct H as [H | [H | H]].
      * simpl. destruct x. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= y \/ idz >= S z)). left. left. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. left. apply H.
      apply block_correct_yz.
      left. left. apply H.
      apply block_correct.
      left. left. apply le_S_n. apply le_S. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      left. left. apply H.
      apply IHy with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= y \/ idz >= S z)). left. right. left. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. right. left. apply H.
      apply block_correct_yz.
      left. right. left. apply le_S_n. apply le_S. apply H.
      apply block_correct.
      left. right. left. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      left. right. left. apply H.
      apply IHy with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= y \/ idz >= S z)). left. right. right. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. right. right. apply le_S_n. apply le_S. apply H.
      apply block_correct_yz.
      left. right. right. apply H.
      apply block_correct.
      left. right. right. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      left. right. right. apply H.
      apply IHy with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
    + destruct H as [H | [H | H]].
      * simpl. destruct x. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= y \/ idz >= S z)). right. left. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      right. left. apply H.
      apply IHy with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= y \/ idz >= S z)). right. right. left.
        apply le_S_n. apply le_S. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      right. right. left. apply H.
      apply IHy with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct x. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= S x \/ idy >= y \/ idz >= S z)). right. right. right. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      right. right. right. apply le_S_n. apply le_S. apply H.
      apply IHy with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition grid_not_contain_larger_on_xyz :
  forall x y z x' y' z' idx idy idz i j k,
    ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= y \/ idz >= z)) ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (build_grid (x,y,z) (x', y', z'))) 0.
Proof.
  induction x.
  - intros. destruct y,z; apply empty.
  - intros y z x' y' z' idx idy idz i j k H.
    destruct H as [H | H].
    + destruct H as [H | [H | H]].
      * simpl. destruct y. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= S y \/ idz >= S z)). left. left. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_xyz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. left. apply H.
      apply block_correct_yz.
      left. left. apply H.
      apply block_correct.
      left. left. apply le_S_n. apply le_S. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      left. left. apply H.
      apply grid_not_contain_larger_on_yz  with (x' := S x') (y' := S y') (z' := S z').
      left. left. apply H.
      apply IHx with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct y. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= S y \/ idz >= S z)). left. right. left. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_xyz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. right. left. apply H.
      apply block_correct_yz.
      left. right. left. apply le_S_n. apply le_S. apply H.
      apply block_correct.
      left. right. left. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      left. right. left. apply H.
      apply grid_not_contain_larger_on_yz  with (x' := S x') (y' := S y') (z' := S z').
      left. right. left. apply H.
      apply IHx with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct y. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= S y \/ idz >= S z)). left. right. right. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_xyz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      left. right. right. apply le_S_n. apply le_S. apply H.
      apply block_correct_yz.
      left. right. right. apply H.
      apply block_correct.
      left. right. right. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      left. right. right. apply H.
      apply grid_not_contain_larger_on_yz  with (x' := S x') (y' := S y') (z' := S z').
      left. right. right. apply H.
      apply IHx with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
    + destruct H as [H | [H | H]].
      * simpl. destruct y. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= S y \/ idz >= S z)). right. left. apply le_S_n. apply le_S. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_xyz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      right. left. apply H.
      apply grid_not_contain_larger_on_yz  with (x' := S x') (y' := S y') (z' := S z').
      right. left. apply H.
      apply IHx with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct y. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= S y \/ idz >= S z)). right. right. left. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_xyz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. right. left. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      right. right. left. apply H.
      apply grid_not_contain_larger_on_yz  with (x' := S x') (y' := S y') (z' := S z').
      right. right. left. apply le_S_n. apply le_S. apply H.
      apply IHx with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
      * simpl. destruct y. apply empty. destruct z. apply empty.
      assert ((i >= x' \/ j >= y' \/ k >= z') \/ (idx >= x \/ idy >= S y \/ idz >= S z)). right. right. right. apply H.
      destruct x',y',z'; simpl; try (
      rewrite empty_z with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_yz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      rewrite empty_xyz with
          (fx' := fun i x => i) (fy' := fun i x => i) (fz' := fun i x => i)
          (x' := 0) (y' := 0) (z' := 0)
          (fx := fun i x => i) (fy := fun i x => i) (fz := fun i x => i);
      apply empty).
      apply cons_neq.
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct_z.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct_yz.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply block_correct.
      right. right. right. intro C. subst. apply Nat.lt_irrefl in H. apply H.
      apply grid_not_contain_larger_on_z  with (x' := S x') (y' := S y') (z' := S z').
      right. right. right. apply le_S_n. apply le_S. apply H.
      apply grid_not_contain_larger_on_yz  with (x' := S x') (y' := S y') (z' := S z').
      right. right. right. apply H.
      apply IHx with (x' := S x') (y' := S y') (z' := S z').
      apply H0.
      intro C. inversion C; subst.
      apply Nat.lt_irrefl in H. apply H.
Qed.

Proposition grid_not_contain_smaller_on_z :
  forall x y z x' y' z' idx idy idz i j k,
    (S idx < x \/ S idy < y) ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_1z x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b)
    (build_grid (x,y,z) (x', y', z'))) 0.
Proof.
  induction z.
  - intros. destruct x,y; apply empty.
  - intros.
    destruct H as [H | H].
    + destruct x. inversion H.
      destruct y. apply empty.
      simpl.
      apply cat_count with (m := 0) (n := 0).
      apply block_correct.
      right. left. intro C; subst.
      apply Nat.lt_irrefl in H. apply H.
      assert (S idx < S x \/ S idy < S y). left. apply H.
      apply IHz with (k := k) (x' := x') (y' := y') (z' := z') (idz := idz) (i := i) (j := j) in H0.
      apply H0.
    + destruct x. apply empty.
      destruct y. inversion H.
      simpl.
      apply cat_count with (m := 0) (n := 0).
      apply block_correct.
      right. right. left. intro C; subst.
      apply Nat.lt_irrefl in H. apply H.
      assert (S idx < S x \/ S idy < S y). right. apply H.
      apply IHz with (k := k) (x' := x') (y' := y') (z' := z') (idz := idz) (i := i) (j := j) in H0.
      apply H0.
Qed.

Proposition grid_not_contain_smaller_on_yz :
  forall x y z x' y' z' idx idy idz i j k,
    (S idx < x) ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_2yz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b)
    (build_grid (x,y,z) (x', y', z'))) 0.
Proof.
  induction y.
  - intros. destruct x,z; apply empty.
  - intros.
    destruct x. inversion H.
    destruct z. apply empty.
    simpl.
    apply cat_count with (m := 0) (n := 0).
    apply cat_count with (m := 0) (n := 0).
    apply block_correct.
    right. left. intro C; subst.
    apply Nat.lt_irrefl in H. apply H.
    apply grid_not_contain_smaller_on_z.
    left. apply H.
    apply IHy with (k := k) (x' := x') (y' := y') (z' := z') (idz := idz) (i := i) (j := j) (z := S z) (idy := idy) in H.
    apply H.
Qed.

Proposition grid_contain_smaller_on_z :
  forall z x y x' y' z' idx idy idz i j k,
    i < x' -> j < y' -> k < z' -> S idx = x -> S idy = y -> idz < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_1z x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (build_grid (x,y,z) (x', y', z'))) 1.
Proof.
  induction z.
  - intros. inversion H4.
  - intros x y x' y' z' idx idy idz i j k Hi Hj Hk Hx Hy Hz.
    destruct x,y.
    inversion Hx. inversion Hx. inversion Hy.
    simpl. inversion Hx. inversion Hy. subst.
    inversion Hz.
    + subst.
      apply cat_count with (m := 1) (n := 0).
      apply block_contain_smaller_on_xyz.
      apply Hi. apply Hj. apply Hk.
      apply grid_not_contain_larger_on_z.
      right. right. right. apply le_n.
    + subst.
      apply cat_count with (m := 0) (n := 1).
      apply block_correct.
      right. right. right.
      intro C; subst. apply Nat.lt_irrefl in H0. apply H0.
      apply IHz.
      apply Hi. apply Hj. apply Hk.
      reflexivity. reflexivity. apply H0.
Qed.

Proposition grid_contain_smaller_on_yz :
  forall y x z x' y' z' idx idy idz i j k,
    i < x' -> j < y' -> k < z' -> S idx = x -> idy < y -> idz < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_2yz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (build_grid (x,y,z) (x', y', z'))) 1.
Proof.
  induction y.
  - intros. inversion H3.
  - intros x z x' y' z' idx idy idz i j k Hi Hj Hk Hx Hy Hz.
    destruct x,z.
    inversion Hx. inversion Hx. inversion Hz.
    simpl. inversion Hx. subst.
    inversion Hy.
    + subst.
      inversion Hz.
      * subst.
        apply cat_count with (m := 1) (n := 0).
        apply cat_count with (m := 1) (n := 0).
        apply block_contain_smaller_on_xyz.
        apply Hi. apply Hj. apply Hk.
        apply grid_not_contain_larger_on_z.
        right. right. right. apply le_n.
        apply grid_not_contain_larger_on_yz.
        right. right. left. apply le_n.
      * subst.
        apply cat_count with (m := 1) (n := 0).
        apply cat_count with (m := 0) (n := 1).
        apply block_correct.
        right. right. right. intro C; subst. apply Nat.lt_irrefl in H0. apply H0.
        apply grid_contain_smaller_on_z.
        apply Hi. apply Hj. apply Hk. reflexivity. reflexivity. apply H0.
        apply grid_not_contain_larger_on_yz.
        right. right. left. apply le_n.
    + subst.
      apply cat_count with (m := 0) (n := 1).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct.
      right. right. left.
      intro C; subst. apply Nat.lt_irrefl in H0. apply H0.
      apply grid_not_contain_smaller_on_z.
      right. apply le_n_S. apply H0.
      apply IHy.
      apply Hi. apply Hj. apply Hk.
      reflexivity. apply H0. apply Hz.
Qed.

Proposition grid_contain_smaller_on_xyz :
  forall x y z x' y' z' idx idy idz i j k,
    i < x' -> j < y' -> k < z' -> idx < x -> idy < y -> idz < z ->
    count ((idx,idy,idz),(i,j,k)) (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (build_grid (x,y,z) (x', y', z'))) 1.
Proof.
  induction x.
  - intros. inversion H2.
  - intros y z x' y' z' idx idy idz i j k Hi Hj Hk Hx Hy Hz.
    destruct y,z.
    inversion Hy. inversion Hy. inversion Hz.
    simpl.
    inversion Hx.
    + subst.
      inversion Hy.
      * subst.
        inversion Hz.
        --  subst.
            apply cat_count with (m := 1) (n := 0).
            apply cat_count with (m := 1) (n := 0).
            apply cat_count with (m := 1) (n := 0).
            apply block_contain_smaller_on_xyz.
            apply Hi. apply Hj. apply Hk.
            apply grid_not_contain_larger_on_z.
            right. right. right. apply le_n.
            apply grid_not_contain_larger_on_yz.
            right. right. left. apply le_n.
            apply grid_not_contain_larger_on_xyz.
            right. left. apply le_n.
        -- subst.
            apply cat_count with (m := 1) (n := 0).
            apply cat_count with (m := 1) (n := 0).
            apply cat_count with (m := 0) (n := 1).
            apply block_correct.
            right. right. right. intro C; subst. apply Nat.lt_irrefl in H0. apply H0.
            apply grid_contain_smaller_on_z.
            apply Hi. apply Hj. apply Hk. reflexivity. reflexivity. apply H0.
            apply grid_not_contain_larger_on_yz.
            right. right. left. apply le_n.
            apply grid_not_contain_larger_on_xyz.
            right. left. apply le_n.
      * subst.
        apply cat_count with (m := 1) (n := 0).
        apply cat_count with (m := 0) (n := 1).
        apply cat_count with (m := 0) (n := 0).
        apply block_correct.
        right. right. left. intro C; subst. apply Nat.lt_irrefl in H0. apply H0.
        apply grid_not_contain_smaller_on_z.
        right. apply le_n_S. apply H0.
        apply grid_contain_smaller_on_yz.
        apply Hi. apply Hj. apply Hk. reflexivity. apply H0. apply Hz.
        apply grid_not_contain_larger_on_xyz.
        right. left. apply le_n.
    + subst.
      apply cat_count with (m := 0) (n := 1).
      apply cat_count with (m := 0) (n := 0).
      apply cat_count with (m := 0) (n := 0).
      apply block_correct.
      right. left.
      intro C; subst. apply Nat.lt_irrefl in H0. apply H0.
      apply grid_not_contain_smaller_on_z.
      left. apply le_n_S. apply H0.
      apply grid_not_contain_smaller_on_yz.
      apply le_n_S. apply H0.
      apply IHx.
      apply Hi. apply Hj. apply Hk.
      apply H0. apply Hy. apply Hz.
Qed.



Proposition grid_correct :
  forall x y z x' y' z' i j k i' j' k',
    ((i' >= x' \/ j' >= y' \/ k' >= z') \/ (i >= x \/ j >= y \/ k >= z)) ->
    count ((i,j,k),(i',j',k')) (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
    (fun (i j k : nat) => (build_block (x',y',z') (i, j, k)))) 0.
Proof.
  apply grid_not_contain_larger_on_xyz.
Qed.

Proposition grid_complete :
  forall x y z x' y' z' i j k i' j' k',
  i' < x' -> j' < y' -> k' < z' -> i < x -> j < y -> k < z ->
  count ((i,j,k),(i',j',k')) (thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) 
  (fun (i j k : nat) => (build_block (x',y',z') (i, j, k)))) 1.
Proof.
  apply grid_contain_smaller_on_xyz.
Qed.


Proposition blocks_correct :
  forall i e m,
  no_error e blocks -> count i (thread_set' e) m -> count i (thread_set' (blocks e)) m
.
Proof.
  induction e; intros; try (exfalso; apply H; reflexivity).
  - destruct shp as [[x y] z], shp' as [[x' y'] z']. simpl in *.
    rewrite grid_ok_xyz in H0. apply H0.
  - simpl in *. assert (forall i n v n0,
          (forall n' n0, n' < n ->
                count i (thread_set' (v n')) n0 ->
                count i (thread_set' (blocks (v n'))) n0) ->
            count i (zip (buildList n (fun i : nat => thread_set' (v i)))) n0 ->
            count i (zip (buildList n (fun i0 : nat => thread_set' (blocks (v i0))))) n0). {
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
                count a (thread_set' (v i j k)) n ->
                count a (thread_set' (blocks (v i j k))) n) ->
            count a (thread_set' (TensorCollection x y z v)) n ->
            count a (thread_set' (blocks (TensorCollection x y z v))) n). {
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



