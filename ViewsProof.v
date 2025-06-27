
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsLemmas.
Require Import PeanoNat.



Definition view {A : List nat} {B : List nat} (f : Tuple B -> Tuple A) : (CurryViewArray A -> CurryViewArray B) :=
  fun v x => v (f x)
.

Definition currying {A : List nat} : ViewArray A -> CurryViewArray A :=
  fun v x => curry_totalApp v x
.

(*
preserve_Injectivity f <-> (fun (g : C -> ViewArray A) x y -> f (g x) y) preserves injectivity of g
*)
Definition preserve_Injectivity {A : List nat} {B : List nat} (f : CurryViewArray A -> CurryViewArray B) :=
  forall (C : List nat) (v : ViewArray (C++A)),
  Injective v ->
  (forall (i j : Tuple C) (x y : Tuple B),
  (f (currying (curry_partialApp v i))) x = (f (currying (curry_partialApp v j))) y -> (i,x) = (j,y)).

Proposition preserve_Injectivity_implies_preserving_view_injectivity :
  forall A B (f : CurryViewArray A -> CurryViewArray B), preserve_Injectivity f ->
  (forall v, Injective v -> (forall x y, (f (currying v)) x = (f (currying v)) y -> x = y)).
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
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx n (n - 1 - to_nat i) reverseProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold identity_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    inversion H.
    apply function_injective in H1.
    subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := fx) in *.
    set (j' := (j,tj)) in *.
    set (y' := fy) in *.
    assert (Heq : (curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> (i',x') = (j',y')).
    apply injectivity_decomposition. apply Hinj.
    simpl in *.
    apply Heq in H.
    unfold i',j',x',y' in *.
    inversion H.
    apply function_injective in H3.
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
  set (function := fun (x : Tuple (b::T)) => match x with | (i,tx) => (idx (b+n) (to_nat i) takeleftProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold identity_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    inversion H.
    apply function_injective in H1.
    subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := fx) in *.
    set (j' := (j,tj)) in *.
    set (y' := fy) in *.
    assert (Heq : (curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> (i',x') = (j',y')).
    apply injectivity_decomposition. apply Hinj.
    simpl in *.
    apply Heq in H.
    unfold i',j',x',y' in *.
    inversion H.
    apply function_injective in H3.
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
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx (a+n) (a+to_nat i) takerightProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold identity_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    inversion H.
    apply function_injective in H1.
    subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := fx) in *.
    set (j' := (j,tj)) in *.
    set (y' := fy) in *.
    assert (Heq : (curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> (i',x') = (j',y')).
    apply injectivity_decomposition. apply Hinj.
    simpl in *.
    apply Heq in H.
    unfold i',j',x',y' in *.
    inversion H.
    apply function_injective in H3.
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
  set (function := fun (x : Tuple ((b-a)::T)) => match x with | (i,tx) => (idx (b+n) (a+to_nat i) selectrangeProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold identity_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    inversion H.
    apply function_injective in H1.
    subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := fx) in *.
    set (j' := (j,tj)) in *.
    set (y' := fy) in *.
    assert (Heq : (curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> (i',x') = (j',y')).
    apply injectivity_decomposition. apply Hinj.
    simpl in *.
    apply Heq in H.
    unfold i',j',x',y' in *.
    inversion H.
    apply function_injective in H3.
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
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (j,(i,tx)) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x1 tx],y as [y1 ty], tx as [x2 tx], ty as [y2 ty].
  intros. unfold identity_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    inversion H.
    try apply function_injective in H1.
    subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := fx) in *.
    set (j' := (j,tj)) in *.
    set (y' := fy) in *.
    assert (Heq : (curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> (i',x') = (j',y')).
    apply injectivity_decomposition. apply Hinj.
    simpl in *.
    apply Heq in H.
    unfold i',j',x',y' in *.
    inversion H.
    try apply function_injective in H3.
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
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) =>
      (idx (m*n) (to_nat j + m*(to_nat i)) groupProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x1 tx],y as [y1 ty], tx as [x2 tx], ty as [y2 ty].
  intros. unfold identity_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    inversion H.
    try apply function_injective in H1; injection H1.
    intros;subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := fx) in *.
    set (j' := (j,tj)) in *.
    set (y' := fy) in *.
    assert (Heq : (curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> (i',x') = (j',y')).
    apply injectivity_decomposition. apply Hinj.
    simpl in *.
    apply Heq in H.
    unfold i',j',x',y' in *.
    inversion H.
    try apply function_injective in H3.
    try injection H3;intros.
    subst;reflexivity.
Qed.


(** map *)
Proposition map_preserves_injectivity :
  forall A B (n : nat) (f : CurryViewArray A -> CurryViewArray B), preserve_Injectivity f -> preserve_Injectivity (map f (n := n)).
Proof.
  unfold preserve_Injectivity.
  intros A B n f Hf C v Hinj i j x y H.
  assert (function_injective : forall (xi yi : Idx n) (tx ty : (Tuple B)),
      (f (currying (curry_partialApp v i xi))) tx = (f (currying (curry_partialApp v j yi))) ty ->
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

Theorem injective_functions_preserve_injectivity :
  forall A B (f : Tuple B -> Tuple A),
  (forall x y, f x = f y -> x = y) -> preserve_Injectivity (view f).
Proof.
  intros A B f Hf C v Hinj i j x y H.
  destruct C.
  + destruct i,j. unfold Injective in Hinj. unfold currying in *. unfold view in *. simpl in *.
  apply Hinj in H. apply Hf in H. subst. reflexivity.
  + destruct i as [i ti],j as [j tj]. unfold currying in *. unfold view in *. simpl in *.
  assert (Heq : curry_totalApp (curry_partialApp v (i,ti) (A := (h::C))) (f x) = curry_totalApp (curry_partialApp v (j,tj) (A := (h::C))) (f y)
        -> ((i,ti),f x) = ((j,tj),f y)).
  apply injectivity_decomposition. apply Hinj. apply Heq in H.
  inversion H. apply Hf in H3. subst. reflexivity.
Qed.
