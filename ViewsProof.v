
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsLemmas.
Require Import PeanoNat.


Definition view {A : List nat} {B : List nat} : (Tuple B -> Tuple A) -> ViewArray A -> ViewArray B :=
  fun f v => uncurry (fun x => curry_totalApp v (f x)).

(*
preserve_Injectivity f <-> (fun (g : C -> ViewArray A) x y -> f (g x) y) preserves injectivity of g
*)
Definition preserve_Injectivity {A : List nat} {B : List nat} (f : ViewArray A -> ViewArray B) :=
  forall (C : List nat) (v : ViewArray (C++A)),
  Injective v ->
  (forall (i j : Tuple C) (x y : Tuple B),
  curry_totalApp (f (curry_partialApp v i)) x = curry_totalApp (f (curry_partialApp v j)) y -> (i,x) = (j,y)).

Proposition preserve_Injectivity_implies_preserving_view_injectivity :
  forall A B (f : ViewArray A -> ViewArray B), preserve_Injectivity f -> (forall v, Injective v -> Injective (f v)).
Proof.
  unfold preserve_Injectivity.
  intros A B f Hf v Hinj x y.
  unfold Injective.
  intros.
  apply Hf with (C := Nil nat) (x := x) (y := y) (i := I) (j := I) in H.
  inversion H.
  reflexivity.
  apply Hinj.
Qed.

(** identity_view *)
Proposition identity_view_injective :
  forall n, Injective (identity_view n).
Proof.
  unfold Injective.
  intros n x y H.
  unfold identity_view in H.
  simpl in H.
  destruct x as [x tx],y as [y ty].
  inversion H.
  apply to_nat_injective in H1.
  destruct tx,ty.
  rewrite H1.
  reflexivity.
Qed.

(** reverse *)
Proposition reverse_preserves_injectivity :
  forall T n, preserve_Injectivity (view reverse) (A := (n::T)).
Proof.
  intros T n C v Hinj i j x y H.
  assert (function_injective : (forall (x y : Idx n), n - 1 - to_nat x = n - 1 - to_nat y -> x = y)). {
    intros x' y' H'. simpl in H'.
    apply sub_injective in H'.
    apply to_nat_injective in H'.
    inversion H. subst. split; reflexivity.
    destruct n. destruct x' as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y' as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  }
  simpl in H.
  destruct x as [x tx],y as [y ty].
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x : Tuple [[T; n]] => curry_totalApp (curry_partialApp v i) (reverse x)) x) tx
          = (fun x => curry_totalApp (curry_partialApp v i) (reverse x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x : Tuple [[T; n]] => curry_totalApp (curry_partialApp v j) (reverse x)) y) ty
          = (fun x => curry_totalApp (curry_partialApp v j) (reverse x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply injectivity_decomposition in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
  apply Hinj.
Qed.

(** take_left *)
Proposition take_left_preserves_injectivity :
  forall T n b, preserve_Injectivity (view (take_left b)) (A := ((b+n)::T)).
Proof.
  intros T n b C v Hinj i j x y H.
  assert (function_injective : (forall (x y : Idx (b)), to_nat x = to_nat y -> x = y)). {
    intros x' y' H'.
    apply to_nat_injective in H'.
    apply H'.
  }
  simpl in H.
  destruct x as [x tx],y as [y ty].
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v i) ((take_left b) x)) x) tx
          = (fun x => curry_totalApp (curry_partialApp v i) ((take_left b) x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v j) ((take_left b) x)) y) ty
          = (fun x => curry_totalApp (curry_partialApp v j) ((take_left b) x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply injectivity_decomposition in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
  apply Hinj.
Qed.

(** take_right *)
Proposition take_right_preserves_injectivity :
  forall T n a, preserve_Injectivity (view (take_right a)) (A := ((a+n)::T)).
Proof.
  intros T n a C v Hinj i j x y H.
  assert (function_injective : (forall (x y : Idx n), a + to_nat x = a + to_nat y -> x = y)). {
    intros x' y' H'.
    apply add_injective in H'.
    apply to_nat_injective in H'.
    apply H'.
  }
  simpl in H.
  destruct x as [x tx],y as [y ty].
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v i) ((take_right a) x)) x) tx
          = (fun x => curry_totalApp (curry_partialApp v i) ((take_right a) x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v j) ((take_right a) x)) y) ty
          = (fun x => curry_totalApp (curry_partialApp v j) ((take_right a) x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply injectivity_decomposition in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
  apply Hinj.
Qed.

(** select_range *)
Proposition select_range_preserves_injectivity :
  forall T n a b, preserve_Injectivity (view (select_range a b)) (A := ((b+n)::T)).
Proof.
  intros T n a b C v Hinj i j x y H.
  assert (function_injective : (forall (x y : Idx (b-a)), a + to_nat x = a + to_nat y -> x = y)). {
    intros x' y' H'.
    apply add_injective in H'.
    apply to_nat_injective in H'.
    apply H'.
  }
  simpl in H.
  destruct x as [x tx],y as [y ty].
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v i) ((select_range a b) x)) x) tx
          = (fun x => curry_totalApp (curry_partialApp v i) ((select_range a b) x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v j) ((select_range a b) x)) y) ty
          = (fun x => curry_totalApp (curry_partialApp v j) ((select_range a b) x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply injectivity_decomposition in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
  apply Hinj.
Qed.

(** transpose *)
Proposition transpose_preserves_injectivity :
  forall T m n, preserve_Injectivity (view transpose) (A := (m::n::T)).
Proof.
  unfold preserve_Injectivity.
  intros T m n C v Hinj i j x y H.
  assert (function_injective : forall (i1 i2 : Idx m) (j1 j2: Idx n), (j1,i1) = (j2,i2) -> (i1,j1) = (i2,j2)).
    intros; inversion H0; subst; reflexivity.
  simpl in H.
  destruct x as [xi tx], tx as [xj tx],y as [yi ty], ty as [yj ty].
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v i) (transpose x)) xi xj) tx
          = (fun x => curry_totalApp (curry_partialApp v i) (transpose x)) (xi, (xj,tx))).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v j) (transpose x)) yi yj) ty
          = (fun x => curry_totalApp (curry_partialApp v j) (transpose x)) (yi, (yj,ty))).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply injectivity_decomposition in H.
  simpl in *.
  inversion H.
  subst;reflexivity.
  apply Hinj.
Qed.


(** group *)
Proposition group_preserves_injectivity :
  forall T m n, preserve_Injectivity (view (group m)) (A := (m*n::T)).
Proof.
  unfold preserve_Injectivity.
  intros T m n C v Hinj i j x y H.
  assert (function_injective :
  forall (xi yi : Idx n) (xj yj : Idx m), to_nat xj + m * to_nat xi = to_nat yj + m * to_nat yi -> (xi,xj) = (yi,yj)). {
    intros. apply projection_injective in H0.
    inversion H0. apply to_nat_injective in H2,H3. subst;reflexivity.
    apply BoundedInt.
    apply BoundedInt.
  }
  simpl in H.
  destruct x as [xi tx], tx as [xj tx],y as [yi ty], ty as [yj ty].
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v i) (group m x)) xi xj) tx
          = (fun x => curry_totalApp (curry_partialApp v i) (group m x)) (xi, (xj,tx))).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (curry_partialApp v j) (group m x)) yi yj) ty
          = (fun x => curry_totalApp (curry_partialApp v j) (group m x)) (yi, (yj,ty))).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply injectivity_decomposition in H.
  inversion H.
  apply projection_injective in H2.
  inversion H2.
  apply to_nat_injective in H4.
  apply to_nat_injective in H5.
  subst;reflexivity.
  apply BoundedInt.
  apply BoundedInt.
  apply Hinj.
Qed.


(** map *)
Proposition map_preserves_injectivity :
  forall A B (n : nat) (f : ViewArray A -> ViewArray B), preserve_Injectivity f -> preserve_Injectivity (map f (n := n)).
Proof.
  unfold preserve_Injectivity.
  intros A B n f Hf C v Hinj i j x y H.
  assert (function_injective : forall (xi yi : Idx n) (tx ty : (Tuple B)),
      curry_totalApp (f (curry_partialApp v i xi)) tx = curry_totalApp (f (curry_partialApp v j yi)) ty ->
      ((xi,i),tx) = ((yi,j),ty)). {
    intros xi yi tx ty H'.
    assert (Hx:curry_partialApp v i xi = curry_partialApp (reorder v) (A := (n::C)) (xi,i)).
    apply reorder_is_correct.
    assert (Hy:curry_partialApp v j yi = curry_partialApp (reorder v) (A := (n::C)) (yi,j)).
    apply reorder_is_correct.
    rewrite Hx,Hy in H'.
    simpl in H'.
    apply Hf with (v := reorder v) (C := (n::C)).
    apply reorder_keeps_injectivity. apply Hinj.
    apply H'.
  }
  simpl in H.
  destruct x as [x tx],y as [y ty].
  apply function_injective in H.
  injection H. intros;subst;split;reflexivity.
Qed.

Theorem injective_function_preserve_injectivity :
  forall A B (f : Tuple B -> Tuple A),
  (forall x y, f x = f y -> x =y) -> preserve_Injectivity (view f).
Proof.
  intros A B f f_inj C v v_inj i j x y H.
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x : Tuple B => curry_totalApp (curry_partialApp v i) (f x))) x =
    curry_totalApp (curry_partialApp v i) (f x)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x : Tuple B => curry_totalApp (curry_partialApp v j) (f x))) y =
    curry_totalApp (curry_partialApp v j) (f y)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  apply injectivity_decomposition in H.
  inversion H.
  apply f_inj in H2.
  subst; reflexivity.
  apply v_inj.
Qed.


