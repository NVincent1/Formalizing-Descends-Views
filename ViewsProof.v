
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
Require Import PeanoNat.


Fixpoint cat {T : Type} (A : List T) (B : List T) : List T :=
  match A with
  | [] => B
  | h::tl => h::(cat tl B)
end.

Notation "A ++ B" := (cat A B).


Fixpoint tupcat {A : List nat} {B : List nat} : Tuple A -> Tuple B -> Tuple (A++B) :=
  match A with
  | [] => fun (_ : Tuple []) (y : Tuple B) => y
  | A => fun (x : Tuple A) (y : Tuple B) => match x with | (i,x) => (i,tupcat x y) end
end.

Fixpoint curry_partialApp {A : List nat} {B : List nat} : ViewArray (A++B) -> Tuple A -> ViewArray B :=
  match A with
  | [] => fun (v : ViewArray ([]++B)) (x : Tuple []) => v
  | A => fun (v : ViewArray (A++B)) (x : Tuple A) => match x with | (x,y) => curry_partialApp (v x) y end
end.

Fixpoint curry_totalApp {A : List nat} : ViewArray A -> Tuple A -> nat :=
  match A with
  | [] => fun (v : ViewArray []) (x : Tuple []) => v
  | A => fun (v : ViewArray A) (x : Tuple A) => match x with | (x,y) => curry_totalApp (v x) y end
end.

Fixpoint reorder {C : List nat} {n : nat} {A : List nat}  : ViewArray (C++[[A;n]]) ->  ViewArray [[C++A;n]] :=
  match C with
  | [] => fun (v : ViewArray ([]++[[A;n]])) x => v x
  | C => fun (v : ViewArray (C++[[A;n]])) x => fun i => reorder (v i) x
end.

Definition Injective {A : List nat} (v : ViewArray A) : Prop :=
  forall x y, (curry_totalApp v x) = (curry_totalApp v y) -> x = y.


Definition preserveInjectivity {A : List nat} {B : List nat} (f : ViewArray A -> ViewArray B) :=
  forall (C : List nat) (v : ViewArray (C++A)),
  Injective v ->
  (forall (i j : Tuple C) (x y : Tuple B),
  curry_totalApp (f (curry_partialApp v i)) x = curry_totalApp (f (curry_partialApp v j)) y -> i = j /\ x = y).

Proposition preserveInjectivity_is_correct :
  forall A B (f : ViewArray A -> ViewArray B), preserveInjectivity f -> (forall v, Injective v -> Injective (f v)).
Proof.
  unfold preserveInjectivity.
  intros.
  unfold Injective.
  intros.
  apply H with (C := Nil nat) (x := x) (y := y) (i := I) (j := I) in H0.
  destruct H0.
  apply H2.
  simpl. apply H1.
Qed.

Proposition to_view_injective :
  forall n, Injective (to_view n).
Proof.
  unfold Injective.
  intros.
  unfold to_view in H.
  simpl in H.
  destruct x,y.
  apply to_nat_injective in H.
  destruct t,t0.
  rewrite H.
  reflexivity.
Qed.

Proposition reverse_preserves_injectivity :
  forall T n (v : ViewArray[[T;n]]), Injective v -> Injective (reverse v).
Proof.
  unfold Injective.
  intros.
  unfold reverse in *.
  destruct x as [x tx],y as [y ty].
  simpl in *.
  apply H with (x := ((Id n (n - 1 - to_nat x) reverseProof),tx)) (y := ((Id n (n - 1 - to_nat y) reverseProof),ty)) in H0.
  injection H0.
  intros.
  apply sub_injective in H2.
  apply to_nat_injective in H2. subst. reflexivity.
  destruct n. destruct x. inversion H3. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  destruct n. destruct y. inversion H3. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
Qed.

Proposition select_preserves_injectivity :
  forall T n (a : nat) (b : nat) (v : ViewArray[[T;b+n]]), Injective v -> Injective (select a b v).
Proof.
  unfold Injective.
  intros.
  unfold select in H0.
  simpl in H0.
  destruct x as [x tx],y as [y ty].
  apply H with (x := ((Id (b + n) (a + to_nat x) selectProof),tx)) (y := ((Id (b + n) (a + to_nat y) selectProof),ty)) in H0.
  injection H0. intros.
  apply add_injective in H2.
  apply to_nat_injective in H2.
  subst. reflexivity.
Qed.

Proposition transpose_preserves_injectivity :
  forall T n m (v : ViewArray[[[[T;n]];m]]), Injective v -> Injective (transpose v).
Proof.
  unfold Injective.
  intros.
  unfold transpose in *.
  destruct x as [ix tx], y as [iy ty], tx as [jx tx], ty as [jy ty].
  simpl in *.
  apply H with (x := (jx,(ix,tx))) (y := (jy,(iy,ty))) in H0.
  injection H0.
  intros.
  subst. reflexivity.
Qed.

Proposition group_preserves_injectivity :
  forall T n m (v : ViewArray[[T;m*n]]), Injective v -> Injective (group m v).
Proof.
  unfold Injective.
  intros.
  unfold group in *.
  destruct x as [ix tx], y as [iy ty], tx as [jx tx], ty as [jy ty].
  simpl in *.
  apply H with (x := ((Id (m * n) (to_nat jx + m * to_nat ix) groupProof),tx)) (y := ((Id (m * n) (to_nat jy + m * to_nat iy) groupProof),ty)) in H0.
  inversion H0.
  apply projection_injective in H2.
  inversion H2.
  apply to_nat_injective in H4, H5.
  subst. reflexivity.
  apply BoundedInt.
  apply BoundedInt.
Qed.

Lemma reorder_is_correct :
  forall C A (n : nat) (v : ViewArray (C++(n::A))) (i : Tuple C) (x : Idx n),
  curry_partialApp v i x = curry_partialApp (reorder v) (A := (n::C)) (x,i).
Proof.
  intros.
  induction C.
  - simpl. reflexivity.
  - destruct i. simpl.
  assert ((curry_partialApp (v i) t x) = curry_partialApp (reorder (v i)) (A := n::C) (B := A) (x, t)).
  apply IHC.
  rewrite H. simpl. reflexivity.
Qed.

Lemma reorder_is_correct_2 :
  forall C A (n : nat) (v : ViewArray (C++(n::A))) (i : Tuple C) (x : Idx n),
  curry_partialApp (reorder v x) i = curry_partialApp v i x.
Proof.
  intros.
  induction C.
  - simpl. reflexivity.
  - destruct i. simpl.
  apply IHC.
Qed.

Lemma decomposition :
  forall C A (v : ViewArray (C++A)) (x : Tuple (C++A)),
  exists (i : Tuple C) (j : Tuple A),
  curry_totalApp v x = curry_totalApp (curry_partialApp v i) j /\ x = (tupcat i j).
Proof.
  intros.
  induction C.
  - simpl in *. exists I,x. split; reflexivity.
  - simpl. destruct x.
  assert (exists (i0 : Tuple C) (j : Tuple A),
        curry_totalApp (v i) t = curry_totalApp (curry_partialApp (v i) i0) j /\ t = tupcat i0 j).
  apply IHC.
  destruct H.
  destruct H.
  exists (i,x).
  exists x0.
  split.
  apply H.
  assert (t = tupcat x x0). apply H.
  subst. reflexivity.
Qed.

Lemma recomposition :
  forall C A (v : ViewArray (C++A)) (i : Tuple C) (j : Tuple A),
  curry_totalApp v (tupcat i j) = curry_totalApp (curry_partialApp v i) j.
Proof.
  induction C.
  - intros. destruct i. simpl in *. reflexivity.
  - intros. destruct i as [i ti].
    simpl in *. apply IHC.
Qed.

Lemma tupcat_injective :
  forall A B (x1 x2 : Tuple A) (y1 y2 : Tuple B),
  tupcat x1 y1 = tupcat x2 y2 -> (x1,y1) = (x2,y2).
Proof.
  intros.
  induction A.
  - destruct x1,x2. simpl in H. subst. reflexivity.
  - destruct x1 as [x1 tx1],x2 as [x2 tx2].
  simpl in H.
  injection H. intros. apply IHA in H0. inversion H0. subst. reflexivity.
Qed.

Proposition reorder_keeps_injectivity :
  forall C A (n : nat) (v : ViewArray (C++(n::A))),
  Injective v -> Injective (reorder v).
Proof.
  intros C A.
  destruct C.
  - intros. simpl in *. unfold Injective in *.
    intros. simpl in *.
    apply H in H0.
    apply H0.
  - unfold Injective.
    intros.
    destruct x as [x1 tx],y as [y1 ty].
    destruct tx as [x2 tx], ty as [y2 ty].
    assert (Hx:exists (i : Tuple (n::h::C)) (j : Tuple A),
    curry_totalApp (reorder v) (x1, (x2, tx)) = curry_totalApp (curry_partialApp (reorder v) (A := n::h::C) i) j
    /\ (x1,(x2,tx)) = tupcat i j).
    apply decomposition.
    destruct Hx as [ix Hx]. destruct Hx as [jx Hx].
    simpl in *.
    destruct ix as [ix1 tix].
    destruct tix as [ix2 tix].
    destruct Hx as [Hx Hi].
    rewrite reorder_is_correct_2 in Hx.
    rewrite Hx in H0.
    assert (Hy:exists (i : Tuple (n::h::C)) (j : Tuple A),
    curry_totalApp (reorder v (C:=h::C)) (y1, (y2, ty)) = curry_totalApp (curry_partialApp (reorder v (C := h::C)) (A := n::h::C) i) j
    /\ (y1,(y2,ty)) = tupcat i j).
    apply decomposition.
    destruct Hy as [iy Hy]. destruct Hy as [jy Hy].
    simpl in *.
    destruct iy as [iy1 tiy].
    destruct tiy as [iy2 tiy].
    destruct Hy as [Hy Hj].
    rewrite reorder_is_correct_2 in Hy.
    rewrite Hy in H0.
    assert (curry_totalApp (curry_partialApp v (A := (h::C)) (ix2,tix)) (ix1,jx) = curry_totalApp v (A := ((h::C)++(n::A))) (tupcat (ix2,tix) (A:=(h::C)) (ix1,jx) (B:=(n::A)))).
    symmetry. apply recomposition with (i := (ix2,tix)) (j := (ix1,jx)).
    simpl in H1. rewrite H1 in H0.
    assert (curry_totalApp (curry_partialApp v (A := (h::C)) (iy2,tiy)) (iy1,jy) = curry_totalApp v (A := ((h::C)++(n::A))) (tupcat (iy2,tiy) (A:=(h::C)) (iy1,jy) (B:=(n::A)))).
    symmetry. apply recomposition with (i := (iy2,tiy)) (j := (iy1,jy)).
    simpl in H2. rewrite H2 in H0.
    rewrite Hi,Hj.
    apply H with (x := (ix2,tupcat tix (ix1,jx) (B := (n::A)))) (y := (iy2,tupcat tiy (iy1,jy) (B := (n::A)))) in H0.
    injection H0.
    intros.
    apply tupcat_injective in H3.
    injection H3.
    intros.
    subst.
    reflexivity.
Qed.

Proposition curry_partialApp_keeps_injectivity :
  forall A B (v : ViewArray (A++B)), Injective v -> (forall i, Injective (curry_partialApp v i)).
Proof.
  intros A B.
  induction A.
  + simpl. intros. apply H.
  + intros. intros. simpl. destruct i.
      assert (Injective (v i)). {
        unfold Injective.
        intros. assert ((i,x) = (i,y)).
        apply H. apply H0. injection H1. trivial.
      }
      apply IHA with (i := t) in H0.
      apply H0.
Qed.


Lemma lemma1 :
  forall A B (v : ViewArray (A++B)),
  Injective v -> (forall (i j : Tuple A) (x y : Tuple B), (curry_totalApp (curry_partialApp v i) x) = (curry_totalApp (curry_partialApp v j) y)-> i = j /\ x = y).
Proof.
  intros.
  destruct A.
  - destruct i,j. simpl in H0. apply H in H0. split. reflexivity. apply H0.
  - destruct i as [i ti],j as [j tj].
  simpl in H0.
  assert (curry_totalApp (curry_partialApp (v i) ti) x = curry_totalApp v (tupcat (i,ti) (A := (h::A)) x)).
  symmetry. apply recomposition with (i := (i,ti)).
  assert (curry_totalApp (curry_partialApp (v j) tj) y = curry_totalApp v (tupcat (j,tj) (A := (h::A)) y)).
  symmetry. apply recomposition with (i := (j,tj)).
  rewrite H1,H2 in H0.
  apply H in H0.
  apply tupcat_injective in H0.
  injection H0.
  intros. subst. split;reflexivity.
Qed.

Proposition reverse_preserves_injectivity2 :
  forall T n, preserveInjectivity reverse (A := (n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  unfold reverse in H0.
  destruct x as [x tx],y as [y ty].
  simpl in H0.
  destruct C.
  - simpl in *. unfold Injective in H.
    apply H with (x := ((Id n (n - 1 - to_nat x) reverseProof),tx)) (y := ((Id n (n - 1 - to_nat y) reverseProof),ty)) in H0.
    inversion H0.
    apply sub_injective in H2.
    apply to_nat_injective in H2. subst. destruct i,j. split; reflexivity.
    destruct n. destruct x. inversion H1. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y. inversion H1. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := ((Id n (n - 1 - to_nat x) reverseProof),tx)) in *.
    set (j' := (j,tj)) in *.
    set (y' := ((Id n (n - 1 - to_nat y) reverseProof),ty)) in *.
    assert ((curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> i' = j' /\ x' = y').
    apply lemma1. apply H.
    simpl in *.
    apply H1 in H0. destruct H0.
    unfold x',y' in H2.
    inversion H2.
    apply sub_injective in H4.
    apply to_nat_injective in H4.
    unfold i',j' in *. inversion H0. subst. split; reflexivity.
    destruct n. destruct x. inversion H3. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y. inversion H3. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
Qed.

Proposition select_preserves_injectivity2 :
  forall T n a b, preserveInjectivity (select a b) (A := (b+n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  destruct x as [x tx],y as [y ty].
  destruct C.
  - unfold select in *.
    unfold Injective in H.
    apply H with (x := ((Id (b + n) (a + to_nat x) selectProof),tx)) (y := ((Id (b + n) (a + to_nat y) selectProof),ty)) in H0.
    inversion H0.
    apply add_injective in H2.
    apply to_nat_injective in H2.
    subst. destruct i,j. split;reflexivity.
  - destruct i as [i ti],j as [j tj].
    set (i' := (i,ti)) in *.
    set (x' := ((Id (b + n) (a + to_nat x) selectProof),tx)) in *.
    set (j' := (j,tj)) in *.
    set (y' := ((Id (b + n) (a + to_nat y) selectProof),ty)) in *.
    assert ((curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> i' = j' /\ x' = y').
    apply lemma1. apply H.
    unfold x',y',i',j' in *.
    apply H1 in H0.
    destruct H0.
    injection H0. intros.
    inversion H2.
    apply add_injective in H6.
    apply to_nat_injective in H6.
    subst. split;reflexivity.
Qed.

Proposition transpose_preserves_injectivity2 :
  forall T m n, preserveInjectivity transpose (A := (m::n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  destruct C.
  - destruct i,j,x as [xi tx], y as [yi ty], tx as [xj tx], ty as [yj ty]. unfold Injective in H.
    simpl in *.
    apply H with (x := (xj,(xi,tx))) (y := (yj,(yi,ty))) in H0.
    injection H0.
    intros.
    subst. split;reflexivity.
  - destruct i as [i ti],j as [j tj].
    destruct x as [xi tx], y as [yi ty], tx as [xj tx], ty as [yj ty].
    set (i' := (i,ti)) in *.
    set (x' := (xj,(xi,tx))) in *.
    set (j' := (j,tj)) in *.
    set (y' := (yj,(yi,ty))) in *.
    assert ((curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> i' = j' /\ x' = y').
    apply lemma1. apply H.
    unfold x',y',i',j' in *.
    apply H1 in H0.
    destruct H0.
    injection H0. injection H2. intros. subst.
    split;reflexivity.
Qed.

Proposition group_preserves_injectivity2 :
  forall T m n, preserveInjectivity (group m) (A := (m*n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  destruct C.
  - destruct i,j,x as [xi tx], y as [yi ty], tx as [xj tx], ty as [yj ty]. unfold Injective in H.
    unfold group in H0.
    simpl in *.
    apply H with
      (x := (Id (m * n) (to_nat xj + m * to_nat xi) groupProof,tx))
      (y := (Id (m * n) (to_nat yj + m * to_nat yi) groupProof,ty))
     in H0.
    inversion H0.
    apply projection_injective in H2.
    injection H2.
    intros.
    apply to_nat_injective in H1,H4.
    subst. split;reflexivity.
    apply BoundedInt.
    apply BoundedInt.
  - destruct i as [i ti],j as [j tj],x as [xi tx], y as [yi ty], tx as [xj tx], ty as [yj ty].
  set (i' := (i,ti)) in *.
  set (x' := (Id (m * n) (to_nat xj + m * to_nat xi) groupProof,tx)) in *.
  set (j' := (j,tj)) in *.
  set (y' := (Id (m * n) (to_nat yj + m * to_nat yi) groupProof,ty)) in *.
  assert ((curry_totalApp (curry_partialApp v i') x') = (curry_totalApp (curry_partialApp v j') y')-> i' = j' /\ x' = y').
  apply lemma1. apply H.
  apply H1 in H0.
  unfold i',j',x',y' in *.
  destruct H0.
  injection H0.
  inversion H2.
  apply projection_injective in H4.
  inversion H4.
  apply to_nat_injective in H6,H7.
  intros. subst. split;reflexivity.
  apply BoundedInt.
  apply BoundedInt.
Qed.


Proposition map_preserves_injectivity :
  forall A B (n : nat) (f : ViewArray A -> ViewArray B), preserveInjectivity f -> preserveInjectivity (map f (n := n)).
Proof.
  unfold preserveInjectivity.
  intros.
  destruct C.
  - destruct i,j,x as [xi tx], y as [yi ty].
    simpl in *.
    unfold map in H1.
    assert (curry_totalApp (f (curry_partialApp v (A := (n::[])) (xi,I))) tx = curry_totalApp (f (curry_partialApp v (A := (n::[])) (yi,I))) ty ->
      (xi,I) = (yi,I) /\ tx = ty).
    apply H with (i := (xi,I)) (j := (yi,I)).
    apply H0.
    simpl in H2.
    apply H2 in H1.
    destruct H1.
    injection H1.
    intros.
    subst.
    split;reflexivity.
  - destruct i as [i ti],j as [j tj],x as [xi tx], y as [yi ty].
    unfold map in *.
    set (v' := reorder v (C := (h::C))).
    assert (curry_partialApp v (A := (h::C)) (i,ti) xi = curry_partialApp (reorder v (C := (h::C))) (A := (n::h::C)) (xi,(i,ti))).
    apply reorder_is_correct.
    assert (curry_partialApp v (A := (h::C)) (j,tj) yi = curry_partialApp (reorder v (C := (h::C))) (A := (n::h::C)) (yi,(j,tj))).
    apply reorder_is_correct.
    simpl in *.
    rewrite H2 in H1.
    rewrite H3 in H1.
    set (i' := (xi,(i,ti))) in *.
    set (x' := tx) in *.
    set (j' := (yi,(j,tj))) in *.
    set (y' := ty) in *.
    assert (curry_totalApp (f (curry_partialApp (reorder v (C := (h::C))) (A := (n::h::C)) i')) x' = curry_totalApp (f (curry_partialApp (reorder v (C := (h::C))) (A := (n::h::C)) j')) y' ->
    i' = j' /\ x' = y').
    apply H.
    apply reorder_keeps_injectivity.
    apply H0.
    unfold i',j',x',y' in *.
    apply H4 in H1.
    destruct H1.
    injection H1.
    intros.
    subst.
    split;reflexivity.
Qed.
