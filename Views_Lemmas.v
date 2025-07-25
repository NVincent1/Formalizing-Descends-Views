
From Views Require Import utils.
From Views Require Import BoundedInt.
From Views Require Import Views.
Require Import PeanoNat.



(* Application viewed with curryfication *)
Fixpoint curry_partialApp  {A : List nat} {B : List nat} : ViewArray (A++B) -> Tuple A -> ViewArray B :=
  match A with
  | [] => fun (v : ViewArray ([]++B)) (x : Tuple []) => v
  | A => fun (v : ViewArray (A++B)) (x : Tuple A) => match x with | (x,y) => curry_partialApp (v x) y end
end.

Fixpoint curry_totalApp {A : List nat} : ViewArray A -> Tuple A -> nat :=
  match A with
  | [] => fun (v : ViewArray []) (x : Tuple []) => v
  | A => fun (v : ViewArray A) (x : Tuple A) => match x with | (x,y) => curry_totalApp (v x) y end
end.

(* v is injective if it does not contain twice the same index of the underlying array *)
Definition Injective {A : List nat} (v : ViewArray A) : Prop :=
  forall x y, (curry_totalApp v x) = (curry_totalApp v y) -> x = y.

Proposition curry_partialApp_keeps_injectivity :
  forall A B (v : ViewArray (A++B)), Injective v -> (forall x, Injective (curry_partialApp v x)).
Proof.
  intros A B.
  induction A.
  + simpl. intros. apply H.
  + intros v Hinj x. simpl. destruct x as [i t].
      assert (H:Injective (v i)). {
        unfold Injective.
        intros x y H. assert ((i,x) = (i,y)).
        apply Hinj. apply H. injection H0. trivial.
      }
      apply IHA with (x := t) in H.
      apply H.
Qed.


Definition partapp {B : List nat} {n : nat} (f : Tuple (n::B) -> nat) (x : Idx n) : Tuple B -> nat :=
  fun y => f (x,y).


Fixpoint uncurry {B : List nat} : (Tuple B -> nat) -> ViewArray B :=
  match B with
  | [] => fun (f : Tuple [] -> nat) => (f I : ViewArray [])
  | n::B => fun (f : (Tuple (n::B) -> nat)) (x : Idx n) => uncurry (partapp f x)
end.

Lemma uncurry_curry_inverse :
  forall A x v, curry_totalApp (uncurry v) (A := A) x = v x.
  intros A x v.
  induction A.
  - destruct x. reflexivity.
  - destruct x. simpl. unfold partapp.
  assert (curry_totalApp (uncurry (fun y : Tuple A => v (i, y))) t = (fun y : Tuple A => v (i, y)) t).
  apply IHA. simpl in H. apply H.
Qed.

Fixpoint tupcat {A : List nat} {B : List nat} : Tuple A -> Tuple B -> Tuple (A++B) :=
  match A with
  | [] => fun (_ : Tuple []) (y : Tuple B) => y
  | A => fun (x : Tuple A) (y : Tuple B) => match x with | (i,x) => (i,tupcat x y) end
end.

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

(* v (x,y) = (v x) y *)
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

(* (v x) y = v (x,y) *)
Lemma recomposition :
  forall C A (v : ViewArray (C++A)) (i : Tuple C) (j : Tuple A),
  curry_totalApp v (tupcat i j) = curry_totalApp (curry_partialApp v i) j.
Proof.
  induction C.
  - intros. destruct i. simpl in *. reflexivity.
  - intros. destruct i as [i ti].
    simpl in *. apply IHC.
Qed.


(* v injective -> (fun (x,y) => v (x,y) is injective) *)
Lemma injectivity_decomposition :
  forall A B (v : ViewArray (A++B)),
  Injective v -> (forall (i j : Tuple A) (x y : Tuple B), (curry_totalApp (curry_partialApp v i) x)
                  = (curry_totalApp (curry_partialApp v j) y)-> (i,x) = (j,y)).
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
    inversion H.
    subst. reflexivity.
Qed.

(* Dimension reordering *)
Fixpoint reorder {C : List nat} {n : nat} {A : List nat}  : ViewArray (C++[[A;n]]) ->  ViewArray [[C++A;n]] :=
  match C with
  | [] => fun (v : ViewArray ([]++[[A;n]])) x => v x
  | C => fun (v : ViewArray (C++[[A;n]])) x => fun i => reorder (v i) x
end.

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
    destruct ix as [ix1 tix].
    destruct tix as [ix2 tix].
    destruct Hx as [Hx Hi].
    simpl in *.
    rewrite <- reorder_is_correct in Hx.
    rewrite Hx in H.
    assert (Hy:exists (i : Tuple (n::h::C)) (j : Tuple A),
    curry_totalApp (reorder v (C:=h::C)) (y1, (y2, ty)) = curry_totalApp (curry_partialApp (reorder v (C := h::C)) (A := n::h::C) i) j
    /\ (y1,(y2,ty)) = tupcat i j).
    apply decomposition.
    destruct Hy as [iy Hy]. destruct Hy as [jy Hy].
    destruct iy as [iy1 tiy].
    destruct tiy as [iy2 tiy].
    destruct Hy as [Hy Hj].
    simpl in *.
    rewrite <- reorder_is_correct in Hy.
    rewrite Hy in H.
    clear Hx. clear Hy.
    assert (Hx:curry_totalApp (curry_partialApp v (A := (h::C)) (ix2,tix)) (ix1,jx)
            = curry_totalApp v (A := ((h::C)++(n::A))) (tupcat (ix2,tix) (A:=(h::C)) (ix1,jx) (B:=(n::A)))).
    symmetry. apply recomposition with (i := (ix2,tix)) (j := (ix1,jx)).
    simpl in Hx. rewrite Hx in H.
    assert (Hy:curry_totalApp (curry_partialApp v (A := (h::C)) (iy2,tiy)) (iy1,jy) =
            curry_totalApp v (A := ((h::C)++(n::A))) (tupcat (iy2,tiy) (A:=(h::C)) (iy1,jy) (B:=(n::A)))).
    symmetry. apply recomposition with (i := (iy2,tiy)) (j := (iy1,jy)).
    simpl in Hy. rewrite Hy in H.
    rewrite Hi,Hj.
    apply Hinj with (x := (ix2,tupcat tix (ix1,jx) (B := (n::A)))) (y := (iy2,tupcat tiy (iy1,jy) (B := (n::A)))) in H.
    inversion H.
    apply tupcat_injective in H2.
    inversion H2.
    subst.
    reflexivity.
Qed.
