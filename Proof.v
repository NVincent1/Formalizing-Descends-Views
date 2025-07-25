
From Views Require Import Injectivity_Lemmas.
From Views Require Import utils.
From Views Require Import BoundedInt.
From Views Require Import Views.
From Views Require Import Views_Lemmas.
Require Import PeanoNat.


Definition view {A : List nat} {B : List nat} : (Tuple B -> Tuple A) -> ViewArray A -> ViewArray B :=
  fun f v => uncurry (fun x => curry_totalApp v (f x)).

(*
preserve_Injectivity f <-> (fun (g : C -> ViewArray A) x y -> f (g x) y) preserves injectivity of g
*)
Definition preserve_Injectivity {A : List nat} {B : List nat} (f : ViewArray A -> ViewArray B) :=
  forall (C : Type) (v : C -> ViewArray A),
  (forall a b x y, curry_totalApp (v a) x = curry_totalApp (v b) y -> (a,x) = (b,y)) ->
  (forall (i j : C) (x y : Tuple B),
  curry_totalApp (f (v i)) x = curry_totalApp (f (v j)) y -> (i,x) = (j,y)).

Proposition preserve_Injectivity_implies_preserving_view_injectivity :
  forall A B (f : ViewArray A -> ViewArray B), preserve_Injectivity f -> (forall v, Injective v -> Injective (f v)).
Proof.
  unfold preserve_Injectivity.
  intros A B f Hf v Hinj x y.
  unfold Injective.
  intros.
  assert ((I,x) = (I,y)). apply Hf with (v := fun x => v).
  intros. apply Hinj in H0. subst. destruct a,b. reflexivity. apply H.
  inversion H0. reflexivity.
Qed.

Theorem injective_function_preserve_injectivity :
  (** An injective reordering function holds the property above *)
  forall A B (f : Tuple B -> Tuple A),
  (forall x y, f x = f y -> x = y) -> preserve_Injectivity (view f).
Proof.
  intros A B f f_inj C v v_inj i j x y H.
  unfold view in H.
  assert (Hx:curry_totalApp (uncurry (fun x : Tuple B => curry_totalApp (v i) (f x))) x =
    curry_totalApp (v i) (f x)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x : Tuple B => curry_totalApp (v j) (f x))) y =
    curry_totalApp (v j) (f y)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  apply v_inj in H.
  inversion H.
  apply f_inj in H2.
  subst; reflexivity.
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
  assert (Hx:curry_totalApp (uncurry (fun x : Tuple [[T; n]] => curry_totalApp (v i) (reverse x)) x) tx
          = (fun x => curry_totalApp (v i) (reverse x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x : Tuple [[T; n]] => curry_totalApp (v j) (reverse x)) y) ty
          = (fun x => curry_totalApp (v j) (reverse x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply Hinj in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
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
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (v i) ((take_left b) x)) x) tx
          = (fun x => curry_totalApp (v i) ((take_left b) x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (v j) ((take_left b) x)) y) ty
          = (fun x => curry_totalApp (v j) ((take_left b) x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply Hinj in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
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
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (v i) ((take_right a) x)) x) tx
          = (fun x => curry_totalApp (v i) ((take_right a) x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (v j) ((take_right a) x)) y) ty
          = (fun x => curry_totalApp (v j) ((take_right a) x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply Hinj in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
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
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (v i) ((select_range a b) x)) x) tx
          = (fun x => curry_totalApp (v i) ((select_range a b) x)) (x, tx)).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (v j) ((select_range a b) x)) y) ty
          = (fun x => curry_totalApp (v j) ((select_range a b) x)) (y, ty)).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply Hinj in H.
  inversion H.
  apply function_injective in H2.
  subst;reflexivity.
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
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (v i) (transpose x)) xi xj) tx
          = (fun x => curry_totalApp (v i) (transpose x)) (xi, (xj,tx))).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (v j) (transpose x)) yi yj) ty
          = (fun x => curry_totalApp (v j) (transpose x)) (yi, (yj,ty))).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply Hinj in H.
  simpl in *.
  inversion H.
  subst;reflexivity.
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
  assert (Hx:curry_totalApp (uncurry (fun x => curry_totalApp (v i) (group m x)) xi xj) tx
          = (fun x => curry_totalApp (v i) (group m x)) (xi, (xj,tx))).
  apply uncurry_curry_inverse.
  rewrite Hx in H.
  assert (Hy:curry_totalApp (uncurry (fun x => curry_totalApp (v j) (group m x)) yi yj) ty
          = (fun x => curry_totalApp (v j) (group m x)) (yi, (yj,ty))).
  apply uncurry_curry_inverse.
  rewrite Hy in H.
  clear Hx. clear Hy.
  intros.
  apply Hinj in H.
  inversion H.
  apply projection_injective in H2.
  inversion H2.
  apply to_nat_injective in H4.
  apply to_nat_injective in H5.
  subst;reflexivity.
  apply BoundedInt.
  apply BoundedInt.
Qed.


(** map *)
Proposition map_preserves_injectivity :
  forall A B (n : nat) (f : ViewArray A -> ViewArray B), preserve_Injectivity f -> preserve_Injectivity (map f (n := n)).
Proof.
  unfold preserve_Injectivity.
  intros A B n f Hf C v Hinj i j x y H.
  simpl in H. destruct x as [hx x], y as [hy y].
  set (v':= (fun x => match x with | (a,n) => v a n end) : (C * Idx n) -> ViewArray A).
  assert (forall a n, map f (v a) n = (f (v' (a,n)))).
    reflexivity.
  rewrite H0 in H.
  rewrite H0 in H.
  assert (Hinj': (forall (a b : (C * Idx n)) (x y : Tuple A),
      curry_totalApp (v' a) x = curry_totalApp (v' b) y -> (a, x) = (b, y))).
    intros. destruct a,b. simpl in H1.
    assert (curry_totalApp (v c i0) x0 = curry_totalApp (v c) (i0,x0)). reflexivity.
    assert (curry_totalApp (v c0 i1) y0 = curry_totalApp (v c0) (i1,y0)). reflexivity.
    rewrite H2,H3 in H1. apply Hinj in H1. inversion H1. reflexivity.
  apply Hf with (i := (i,hx)) (j := (j,hy)) (x := x) (y := y) in Hinj'.
  inversion Hinj'. reflexivity.
  apply H.
Qed.


