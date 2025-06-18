
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

Definition curry_Injective {A : List nat} {B : List nat} (f : ViewArray A -> ViewArray B) :=
  forall (C : List nat) (v : ViewArray (C++A)),
  Injective v ->
  (forall (i j : Tuple C) (x y : Tuple B),
  curry_totalApp (f (curry_partialApp v i)) x = curry_totalApp (f (curry_partialApp v j)) y -> (i,x) = (j,y)).

Proposition curry_Injective_implies_preserving_injectivity :
  forall A B (f : ViewArray A -> ViewArray B), curry_Injective f -> (forall v, Injective v -> Injective (f v)).
Proof.
  unfold curry_Injective.
  intros A B f Hf v Hinj x y.
  unfold Injective.
  intros.
  apply Hf with (C := Nil nat) (x := x) (y := y) (i := I) (j := I) in H.
  inversion H.
  reflexivity.
  apply Hinj.
Qed.

Proposition to_view_injective :
  forall n, Injective (to_view n).
Proof.
  unfold Injective.
  intros n x y H.
  unfold to_view in H.
  simpl in H.
  destruct x as [x tx],y as [y ty].
  apply to_nat_injective in H.
  destruct tx,ty.
  rewrite H.
  reflexivity.
Qed.

Lemma reorder_is_correct :
  forall C A (n : nat) (v : ViewArray (C++(n::A))) (i : Tuple C) (x : Idx n),
  curry_partialApp v i x = curry_partialApp (reorder v x) i.
Proof.
  intros.
  induction C.
  - simpl. reflexivity.
  - destruct i as [i t]. simpl.
  assert ((curry_partialApp (v i) t x) = curry_partialApp (reorder (v i)) (A := n::C) (B := A) (x, t)).
  apply IHC.
  rewrite H. simpl. reflexivity.
Qed.

Lemma decomposition :
  forall C A (v : ViewArray (C++A)) (x : Tuple (C++A)),
  exists (i : Tuple C) (j : Tuple A),
  curry_totalApp v x = curry_totalApp (curry_partialApp v i) j /\ x = (tupcat i j).
Proof.
  intros.
  induction C.
  - simpl in *. exists I,x. split; reflexivity.
  - simpl. destruct x as [x tx].
  assert (exists (i : Tuple C) (j : Tuple A),
        curry_totalApp (v x) tx = curry_totalApp (curry_partialApp (v x) i) j /\ tx = tupcat i j).
  apply IHC.
  destruct H as [c H].
  destruct H as [a H].
  exists (x,c).
  exists a.
  split.
  apply H.
  assert (tx = tupcat c a). apply H.
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
  injection H. intros Htupcat Hx. apply IHA in Htupcat. inversion Htupcat. subst. reflexivity.
Qed.

Proposition reorder_keeps_injectivity :
  forall C A (n : nat) (v : ViewArray (C++(n::A))),
  Injective v -> Injective (reorder v).
Proof.
  intros C A.
  destruct C.
  - intros n v Hinj. simpl in *. unfold Injective in *.
    intros x y H. simpl in *.
    apply Hinj in H.
    apply H.
  - unfold Injective.
    intros n v Hinj x y H.
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
    rewrite <- reorder_is_correct in Hx.
    rewrite Hx in H.
    assert (Hy:exists (i : Tuple (n::h::C)) (j : Tuple A),
    curry_totalApp (reorder v (C:=h::C)) (y1, (y2, ty)) = curry_totalApp (curry_partialApp (reorder v (C := h::C)) (A := n::h::C) i) j
    /\ (y1,(y2,ty)) = tupcat i j).
    apply decomposition.
    destruct Hy as [iy Hy]. destruct Hy as [jy Hy].
    simpl in *.
    destruct iy as [iy1 tiy].
    destruct tiy as [iy2 tiy].
    destruct Hy as [Hy Hj].
    rewrite <- reorder_is_correct in Hy.
    rewrite Hy in H.
    clear Hx. clear Hy.
    assert (Hx:curry_totalApp (curry_partialApp v (A := (h::C)) (ix2,tix)) (ix1,jx) = curry_totalApp v (A := ((h::C)++(n::A))) (tupcat (ix2,tix) (A:=(h::C)) (ix1,jx) (B:=(n::A)))).
    symmetry. apply recomposition with (i := (ix2,tix)) (j := (ix1,jx)).
    simpl in Hx. rewrite Hx in H.
    assert (Hy:curry_totalApp (curry_partialApp v (A := (h::C)) (iy2,tiy)) (iy1,jy) = curry_totalApp v (A := ((h::C)++(n::A))) (tupcat (iy2,tiy) (A:=(h::C)) (iy1,jy) (B:=(n::A)))).
    symmetry. apply recomposition with (i := (iy2,tiy)) (j := (iy1,jy)).
    simpl in Hy. rewrite Hy in H.
    rewrite Hi,Hj.
    apply Hinj with (x := (ix2,tupcat tix (ix1,jx) (B := (n::A)))) (y := (iy2,tupcat tiy (iy1,jy) (B := (n::A)))) in H.
    injection H.
    intros Hcat Heq.
    apply tupcat_injective in Hcat.
    injection Hcat.
    intros;subst.
    reflexivity.
Qed.

Proposition curry_partialApp_keeps_injectivity :
  forall A B (v : ViewArray (A++B)), Injective v -> (forall i, Injective (curry_partialApp v i)).
Proof.
  intros A B.
  induction A.
  + simpl. intros. apply H.
  + intros v Hinj i. simpl. destruct i.
      assert (H:Injective (v i)). {
        unfold Injective.
        intros x y H. assert ((i,x) = (i,y)).
        apply Hinj. apply H. injection H0. trivial.
      }
      apply IHA with (i := t) in H.
      apply H.
Qed.


Lemma injectivity_decomposition :
  forall A B (v : ViewArray (A++B)),
  Injective v -> (forall (i j : Tuple A) (x y : Tuple B), (curry_totalApp (curry_partialApp v i) x) = (curry_totalApp (curry_partialApp v j) y)-> (i,x) = (j,y)).
Proof.
  intros A B v Hinj i j x y H.
  destruct A.
  - destruct i,j. simpl in H. apply Hinj in H. subst;reflexivity.
  - destruct i as [i ti],j as [j tj].
    simpl in H.
    assert (Hx:curry_totalApp (curry_partialApp (v i) ti) x = curry_totalApp v (tupcat (i,ti) (A := (h::A)) x)).
    symmetry. apply recomposition with (i := (i,ti)).
    assert (Hy:curry_totalApp (curry_partialApp (v j) tj) y = curry_totalApp v (tupcat (j,tj) (A := (h::A)) y)).
    symmetry. apply recomposition with (i := (j,tj)).
    rewrite Hx,Hy in H.
    apply Hinj in H.
    apply tupcat_injective in H.
    injection H.
    intros; subst. reflexivity.
Qed.

Proposition reverse_preserves_injectivity :
  forall T n, curry_Injective reverse (A := (n::T)).
Proof.
  intros T n C v Hinj i j x y H.
  assert (function_injective : (forall x y, reverse (to_view n) x = reverse (to_view n) y -> x = y)). {
    intros x' y' H'. unfold reverse, to_view in H'. simpl in H'.
    apply sub_injective in H'.
    apply to_nat_injective in H'.
    inversion H. subst. split; reflexivity.
    destruct n. destruct x' as [nx Hx]. inversion Hx. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
    destruct n. destruct y' as [ny Hy]. inversion Hy. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply BoundedInt.
  }
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx n (reverse (to_view n) i) reverseProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold to_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    (* Generate goal
    (idx n (reverse (to_view n) x) reverseProof, tx) = (idx n (reverse (to_view n) y) reverseProof, ty)
    -> x,tx = y,ty *)
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

Proposition take_left_preserves_injectivity :
  forall T n b, curry_Injective (take_left b) (A := ((b+n)::T)).
Proof.
  intros T n b C v Hinj i j x y H.
  assert (function_injective : (forall x y, (take_left b) (to_view (b+n)) x = (take_left b) (to_view (b+n)) y -> x = y)). {
    intros x' y' H'. unfold take_left, to_view in H'. simpl in H'.
    apply to_nat_injective in H'.
    apply H'.
  }
  set (function := fun (x : Tuple (b::T)) => match x with | (i,tx) => (idx (b+n) (to_nat i) takeleftProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold to_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    (* Generate goal
    (idx (b + n) (to_nat x) takeleftProof, tx) = (idx (b + n) (to_nat y) takeleftProof, ty)
    -> x,tx = y,ty *)
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

Proposition take_right_preserves_injectivity :
  forall T n a, curry_Injective (take_right a) (A := ((a+n)::T)).
Proof.
  intros T n a C v Hinj i j x y H.
  assert (function_injective : (forall x y, (take_right a) (to_view (a+n)) x = (take_right a) (to_view (a+n)) y -> x = y)). {
    intros x' y' H'. unfold take_right, to_view in H'. simpl in H'.
    apply add_injective in H'.
    apply to_nat_injective in H'.
    apply H'.
  }
  set (function := fun (x : Tuple ((n-a)::T)) => match x with | (i,tx) => (idx (a+n) (a+to_nat i) takerightProof,tx) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x tx],y as [y ty].
  intros. unfold to_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    (* Generate goal
    (idx (a + n) (a + to_nat x) takerightProof, tx) = (idx (a + n) (a + to_nat y) takerightProof, ty)
    -> x,tx = y,ty *)
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

Proposition transpose_preserves_injectivity :
  forall T m n, curry_Injective transpose (A := (m::n::T)).
Proof.
  unfold curry_Injective.
  intros T m n C v Hinj i j x y H.
  assert (function_injective : True). trivial.
  set (function := fun (x : Tuple (n::m::T)) => match x with | (i,(j,tx)) => (j,(i,tx)) end).
  simpl in H.
  set (fx := function x).
  set (fy := function y).
  destruct x as [x1 tx],y as [y1 ty], tx as [x2 tx], ty as [y2 ty].
  intros. unfold to_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    (* Generate goal
    (x2, (x1, tx)) = (y2, (y1, ty))
    -> x1,x2,tx = y1,y2,ty *)
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


Proposition group_preserves_injectivity :
  forall T m n, curry_Injective (group m) (A := (m*n::T)).
Proof.
  unfold curry_Injective.
  intros T m n C v Hinj i j x y H.
  assert (function_injective : forall (xi yi : Idx n) (xj yj : Idx m), to_nat xj + m * to_nat xi = to_nat yj + m * to_nat yi -> (xi,xj) = (yi,yj)). {
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
  intros. unfold to_view in function_injective,fx,fy; simpl in function_injective,fx,fy.
  destruct C.
  - simpl in *. unfold Injective in Hinj.
    destruct i,j.
    apply Hinj with (x := fx) (y := fy) in H.
    unfold fx,fy in H.
    (* Generate goal
    (idx (m * n) (to_nat x2 + m * to_nat x1) groupProof, tx) = (idx (m * n) (to_nat y2 + m * to_nat y1) groupProof, ty)
    -> (x1,x2,tx) = (y1,y2,ty) *)
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


Proposition map_preserves_injectivity :
  forall A B (n : nat) (f : ViewArray A -> ViewArray B), curry_Injective f -> curry_Injective (map f (n := n)).
Proof.
  unfold curry_Injective.
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

