
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
Require Import PeanoNat.


Proposition to_view_injective :
  forall n, Injective (to_view n).
Proof.
  unfold Injective.
  split.
  intros.
  unfold to_view in H.
  apply to_nat_injective in H.
  apply H.
  intro. apply I.
Qed.

Proposition reverse_preserves_injectivity :
  forall T n (v : ViewArray[[T;n]]), Injective v -> Injective (reverse v).
Proof.
  unfold Injective.
  intros.
  destruct H.
  unfold reverse in *.
  split.
  - intros. apply H in H1.
  destruct x,y.
  inversion H1.
  apply sub_injective with (c := n-1) in H5.
  subst. apply unif_Idx.
  destruct n. inversion H2. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply H2.
  destruct n. inversion H3. simpl. rewrite Nat.sub_0_r. apply le_S_n. apply H3.
  - intros. apply H0.
Qed.

Proposition select_preserves_injectivity :
  forall T n (a : nat) (b : nat) (v : ViewArray[[T;b+n]]), Injective v -> Injective (select a b v).
Proof.
  unfold Injective.
  intros.
  split.
  - intros. destruct H. unfold select in H0.
  apply H in H0.
  inversion H0.
  apply add_injective in H3.
  apply to_nat_injective in H3.
  apply H3.
  - intros. apply H.
Qed.

Proposition transpose_preserves_injectivity :
  forall T n m (v : ViewArray[[[[T;n]];m]]), Injective v -> Injective (transpose v).
Proof.
  unfold Injective.
  split.
  - intros.
  unfold transpose in H0.
  apply FunOverlap in H0.
  destruct H0.
  destruct H0.
  assert (v x0 = v x1).
  apply FunOverlap. exists x. exists y. apply H0. apply H in H1. subst.
  destruct H.
  destruct H1 with (i := x1).
  apply H2 in H0. apply H0.
  - intros. split.
    + destruct H. intros. unfold transpose in H1.
  assert (v x = v y). apply FunOverlap. exists i,i. apply H1. apply H in H2. apply H2.
    + destruct H. intro. unfold transpose. destruct H0 with (i := i0).
  apply H2.
Qed.

Proposition group_preserves_injectivity :
  forall T n m (v : ViewArray[[T;m*n]]), Injective v -> Injective (group m v).
Proof.
  unfold Injective.
  intros.
  destruct H.
  split.
  - intros. unfold group in H1.
  apply FunOverlap in H1. destruct H1. destruct H1. apply H in H1.
  inversion H1. apply projection_injective in H3. injection H3. intros. apply to_nat_injective in H2. apply H2.
  apply BoundedInt. apply BoundedInt.
  - split.
    + intros. unfold group in H1. apply H in H1.
    inversion H1. apply projection_injective in H3. injection H3. intro. apply to_nat_injective in H2. apply H2.
    apply BoundedInt. apply BoundedInt.
    + intro. unfold group. apply H0.
Qed.

Fixpoint cat {T : Type} (A : List T) (B : List T) : List T :=
  match A with
  | [] => B
  | h::tl => h::(cat tl B)
end.

Notation "A ++ B" := (cat A B).

Fixpoint curry_partialApp {A : List nat} {B : List nat} : ViewArray (A++B) -> Tuple A -> ViewArray B :=
  match A with
  | [] => fun (v : ViewArray ([]++B)) (x : Tuple []) => v
  | A => fun (v : ViewArray (A++B)) (x : Tuple A) => match x with | (x,y) => curry_partialApp (v x) y end
end.

Fixpoint reorder {C : List nat} {n : nat} {A : List nat}  : ViewArray (C++[[A;n]]) ->  ViewArray [[C++A;n]] :=
  match C with
  | [] => fun (v : ViewArray ([]++[[A;n]])) x => v x
  | C => fun (v : ViewArray (C++[[A;n]])) x => fun i => reorder (v i) x
end.

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

Definition preserveInjectivity {A : List nat} {B : List nat} (f : ViewArray A -> ViewArray B) :=
  forall (C : List nat) (v : ViewArray (C++A)),
  Injective v ->
      (forall i : Tuple C, Injective (f (curry_partialApp v i)))
      /\ (forall i j : Tuple C, f (curry_partialApp v i) = f (curry_partialApp v j) -> i = j).

Proposition preserveInjectivity_preserves_injectivity :
  forall A B (f : ViewArray A -> ViewArray B), preserveInjectivity f -> (forall v, Injective v -> Injective (f v)).
Proof.
  unfold preserveInjectivity.
  intros.
  apply H with (C := Nil nat) in H0.
  destruct H0. simpl in H0. apply H0. apply I.
Qed.

Proposition curry_partialApp_keeps_injectivity :
  forall A B (v : ViewArray (A++B)), Injective v -> (forall i, Injective (curry_partialApp v i)).
Proof.
  intros A B.
  induction A.
  + simpl. intros. apply H.
  + intros. destruct H. intros. simpl. destruct i.
      assert (Injective (v i)). apply H0.
      apply IHA with (i := t) in H1.
      apply H1.
Qed.

Lemma reorder_keeps_injectivity :
  forall C A (n : nat) (v : ViewArray (C++(n::A))),
  Injective v -> Injective (reorder v).
Proof.
  intros.
  unfold Injective.
  split.
  - intros.
    induction C.
    + simpl in H0. apply H. apply H0.
Admitted.


Proposition curry_partialApp_injective :
  forall A B (v : ViewArray (A++B)), Injective v -> (forall i j, (curry_partialApp v i) = (curry_partialApp v j) -> i = j).
Proof.
  intros A B.
  induction A.
  - destruct i,j. reflexivity.
  - destruct i,j. intros. destruct H.
    simpl in *.
    
Admitted.

Proposition reverse_preserves_injectivity2 :
  forall T n, preserveInjectivity reverse (A := (n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  split.
  - intro i. apply curry_partialApp_keeps_injectivity with (i := i) in H.
  apply reverse_preserves_injectivity in H. apply H.
  - intros. unfold reverse in H0. apply FunOverlap in H0.
    destruct H0; destruct H0.
    assert (curry_partialApp v i = curry_partialApp v j).
    apply FunOverlap. exists (Id n (n - 1 - to_nat x) reverseProof), (Id n (n - 1 - to_nat x0) reverseProof).
    apply H0.
    apply curry_partialApp_injective with (i := i) (j := j) in H. apply H. apply H1.
Qed.

Proposition select_preserves_injectivity2 :
  forall T n a b, preserveInjectivity (select a b) (A := (b+n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  split.
  - intro i. apply curry_partialApp_keeps_injectivity with (i := i) in H.
  apply select_preserves_injectivity with (a := a) in H. apply H.
  - intros. unfold select in H0. apply FunOverlap in H0.
    destruct H0; destruct H0.
    assert (curry_partialApp v i = curry_partialApp v j).
    apply FunOverlap. exists (Id (b + n) (a + to_nat x) selectProof), (Id (b + n) (a + to_nat x0) selectProof).
    apply H0.
    apply curry_partialApp_injective with (i := i) (j := j) in H. apply H. apply H1.
Qed.

Proposition transpose_preserves_injectivity2 :
  forall T m n, preserveInjectivity transpose (A := (m::n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  split.
  - intro i. apply curry_partialApp_keeps_injectivity with (i := i) in H.
  apply transpose_preserves_injectivity in H. apply H.
  - intros. unfold transpose in H0. apply FunOverlap in H0.
    destruct H0; destruct H0.
    apply FunOverlap in H0.
    destruct H0; destruct H0.
    assert (curry_partialApp v i = curry_partialApp v j).
    apply FunOverlap. exists x1,x2.
    apply FunOverlap. exists x,x0.
    apply H0.
    apply curry_partialApp_injective with (i := i) (j := j) in H. apply H. apply H1.
Qed.

Proposition group_preserves_injectivity2 :
  forall T m n, preserveInjectivity (group m) (A := (m*n::T)).
Proof.
  unfold preserveInjectivity.
  intros.
  split.
  - intro i. apply curry_partialApp_keeps_injectivity with (i := i) in H.
  apply group_preserves_injectivity in H. apply H.
  - intros. unfold group in H0. apply FunOverlap in H0.
    destruct H0; destruct H0.
    apply FunOverlap in H0.
    destruct H0; destruct H0.
    assert (curry_partialApp v i = curry_partialApp v j).
    apply FunOverlap. exists (Id (m * n) (to_nat x1 + m * to_nat x) groupProof),(Id (m * n) (to_nat x2 + m * to_nat x0) groupProof).
    apply H0.
    apply curry_partialApp_injective with (i := i) (j := j) in H. apply H. apply H1.
Qed.

Proposition map_preserves_injectivity :
  forall A B (n : nat) (f : ViewArray A -> ViewArray B), preserveInjectivity f -> preserveInjectivity (map f (n := n)).
Proof.
  intros.
  unfold preserveInjectivity in H.
  split; set (v' := reorder v).
  - assert (Injective v'). apply reorder_keeps_injectivity. apply H0.
    unfold map. intros. simpl. split.
    + intros.
    apply H with (C := (n::C)) in H1.
    destruct H1.
    assert (curry_partialApp v i x = curry_partialApp v' (A := (n::C)) (x,i)). apply reorder_is_correct.
    assert (curry_partialApp v i y = curry_partialApp v' (A := (n::C)) (y,i)). apply reorder_is_correct.
    rewrite H4 in H2. rewrite H5 in H2.
    apply H3 in H2.
    injection H2. trivial.
    + intros. unfold preserveInjectivity in H.
    apply H with (C := (n::C)) in H1.
    destruct H1.
    assert (curry_partialApp v i i0 = curry_partialApp v' (A := (n::C)) (i0,i)). apply reorder_is_correct.
    rewrite H3.
    apply H1.
  - assert (Injective v'). apply reorder_keeps_injectivity. apply H0.
  unfold map.
  intros. apply H with (C := (n::C)) in H1.
  simpl in *.
  destruct H1.
  assert (forall x, curry_partialApp v i x = curry_partialApp v' (A := (n::C)) (x,i)). apply reorder_is_correct.
  assert (forall x, curry_partialApp v j x = curry_partialApp v' (A := (n::C)) (x,j)). apply reorder_is_correct.
  apply FunOverlap in H2. destruct H2. destruct H2.
  rewrite H4 with (x := x) in H2. rewrite H5 with (x := x0) in H2.
  simpl in H2.
  apply H3 with (i := (x,i)) (j := (x0,j)) in H2. injection H2. intros. apply H6.
Qed.
