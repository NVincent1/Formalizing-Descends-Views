
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import lemmas.
From Views.Execution_resources Require Import blocks.
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




