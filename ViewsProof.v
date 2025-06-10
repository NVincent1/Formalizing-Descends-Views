
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
Require Import PeanoNat.

Inductive List (T : Type) : Type :=
  | Nil : List T
  | Cons (h : T) (tl : List T) : List T
.

Axiom FunEquality :
  forall (T1 : Type) (T2 : Type) (f : T1 -> T2) (g : T1 -> T2),
  f = g <-> forall (x : T1), f x = g x
.


Notation "h :: tl" := (Cons _ h tl).
Notation "[]" := (Nil _).


Fixpoint Tuple (d : List nat) : Type :=
  match d with
  | [] => True
  | n::tl => Idx n * (Tuple tl)
end.

Definition ViewArray (d : List nat) : Type :=
  Tuple d -> nat
.

Notation "[[ T ; n ]]" := (n::T).
Notation "[[ ; n ]]" := [[ [] ; n]].

Definition to_view (n : nat) : ViewArray [[ ; n]] :=
  fun i => match i with | (i,_) => to_nat i end.


Definition reverse {T : List nat} {n : nat}  (v : ViewArray [[T;n]]) : ViewArray [[T;n]] :=
  fun (i : Tuple (n::T)) =>
      match i with | (i,j) =>
      v (to_Idx n (n - 1 - (to_nat i)) reverseProof, j)
      end
.

Definition select  {T :List nat} {l : nat} (a : nat) (b : nat) (v : ViewArray [[T;b + l]]) : ViewArray[[T;b - a]] :=
  fun (i : Tuple ((b-a)::T)) =>
      match i with | (i,j) =>
      v (to_Idx (b+l) (a + to_nat i) selectProof, j)
      end
.

Definition group {T : List nat} (m : nat) (n : nat) (v : ViewArray [[T;m*n]]) : ViewArray [[ [[T;m]] ; n]] :=
  fun (i : Tuple (n::m::T)) =>
      match i with | (i,(j,k)) =>
      v (to_Idx (m*n) (to_nat j + m*(to_nat i)) groupProof,k)
  end
.

Definition transpose {T : List nat} {m : nat} {n : nat} (v : ViewArray [[ [[T;m]] ; n]]) : ViewArray [[ [[T;n]] ; m]] :=
  fun (i : Tuple (m::n::T)) =>
    match i with | (i,(j,k)) =>
    v (j,(i,k))
  end
.

Definition partialApp {T : List nat} {n : nat} : ViewArray [[T;n]] -> Idx n -> (ViewArray T) :=
  fun (v : ViewArray [[T;n]]) i x => v (i,x)
.

Definition map {A : List nat} {B : List nat} {n : nat} (f : (ViewArray A -> ViewArray B))  (v : ViewArray [[A;n]]) : ViewArray [[B;n]] :=
  fun (i : Tuple (n::B)) =>
      match i with | (i,j) =>
      (f (partialApp v i)) j
  end
.

(* The reason we use tuples is that we want total application in this property *)
Definition isInjective {T : List nat} (f : ViewArray T) : Prop :=
  forall (i : Tuple T) (j : Tuple T), f i = f j -> i = j
.

(* A function conserve injectivity if it is injective on indexes and if an array is injective,
then fun (i x) => f (partialApp v i) x is injective *)
Definition conserveInjectivity {A : List nat} {B : List nat} (f : ViewArray A -> ViewArray B) : Prop :=
  forall (n : nat) (v : ViewArray [[A;n]]),
  isInjective v -> (forall (i : Idx n) (j : Idx n) (x : Tuple B) (y : Tuple B), f (partialApp v i) x = f (partialApp v j) y -> x = y /\ i = j)
.

Proposition conserveInjectiviy_conserves_injectiviy :
  forall A B (f : ViewArray A -> ViewArray B), conserveInjectivity f -> (forall v, isInjective v -> isInjective (f v)).
Proof.
  unfold conserveInjectivity.
  unfold isInjective.
  intros.
  assert (isInjective (fun (x : Tuple (1::A)) => match x with | (i,n) => v n end)). {
    unfold isInjective. intros.
    destruct i0; destruct j0. destruct i0; destruct i1. inversion H3.
    inversion H4. subst. apply H0 in H2. rewrite H2. assert (Id 1 0 H3 = Id 1 0 H4). apply unif_Idx. rewrite H5.
    reflexivity.
    inversion H7. inversion H6.
  } set (v' := fun x : Tuple [[A; 1]] => let (_, n) := x in v n) in *.
  unfold isInjective in H2.
  unfold partialApp in *.
  assert (forall (a b : Idx 1) (x y : Tuple B), f (fun x0 : Tuple A => v' (a, x0)) x = f (fun x0 : Tuple A => v' (b, x0)) y -> x = y /\ a = b).
  intros. apply H with (i := a) (j := b) (x := x) (y := y) in H2. apply H2. apply H3.
  assert (0 < 1). apply le_n. 
  assert (f (fun x0 => v' ((Id 1 0 H4),x0)) i = f (fun x0 => v' (Id 1 0 H4,x0)) j).
  unfold v'. assert ((fun x0 => v x0) = v). apply FunEquality. intro. reflexivity.
  rewrite H5. apply H1.
  apply H3 in H5. destruct H5. apply H5.
Qed.

Proposition to_view_is_injective :
  forall (n : nat), isInjective (to_view n).
Proof.
  unfold isInjective. unfold to_view. intros.
  destruct i,j. apply to_nat_injective in H. rewrite H. destruct t,t0. reflexivity.
Qed.

Proposition reverse_conserve_injectivity :
  forall T (n : nat), conserveInjectivity reverse (A := n::T) (B := n::T).
Proof.
  intros. unfold conserveInjectivity. unfold partialApp. intros.
    unfold isInjective in H. unfold reverse in H0. destruct x; destruct y. apply H in H0. injection H0.
    intros. apply sub_injective with (c := n - 1) in H2. apply to_nat_injective in H2. subst. split; reflexivity.
    destruct n. destruct i0. inversion H4. simpl. rewrite Nat.sub_0_r. destruct i0. simpl. apply le_S_n. apply H4.
    destruct n. destruct i1. inversion H4. simpl. rewrite Nat.sub_0_r. destruct i1. simpl. apply le_S_n. apply H4.
Qed.

Proposition select_conserve_injectivity :
  forall T (a : nat) (b : nat) (k : nat), conserveInjectivity (select a b) (A := [[T;b+k]]).
Proof.
  unfold conserveInjectivity.
  unfold select.
  intros.
  - destruct x as [i0 xi]; destruct y as [j0 xj]. apply H in H0. inversion H0. apply add_injective in H3.
  apply to_nat_injective in H3. rewrite H3. split; reflexivity.
Qed.

Proposition group_conserve_injectivity:
  forall T (m : nat) (n : nat), conserveInjectivity (group m n) (A := [[T;m*n]]).
Proof.
  unfold conserveInjectivity. unfold group.
  intros.
  destruct x as [i1 j1]; destruct y as [i2 j2].
  - destruct j1 as [j1 x1]; destruct j2 as [j2 x2]. apply H in H0. inversion H0. assert ((to_nat j1,to_nat i1) = (to_nat j2,to_nat i2)). apply projection_injective with (k := m). apply BoundedInt. apply BoundedInt. apply H3.
  injection H1. intros. apply to_nat_injective in H5. rewrite H5.  apply to_nat_injective in H6. rewrite H6. split; reflexivity.
Qed.

Proposition transpose_conserve_injectivity :
  forall T (m : nat) (n : nat), conserveInjectivity transpose (A := [[[[T;m]];n]]).
Proof.
  unfold conserveInjectivity. unfold transpose.
  intros.
  destruct x as [i1 j1]; destruct y as [i2 j2].
  - destruct j1 as [j1 x1]; destruct j2 as [j2 x2]. apply H in H0. injection H0. intros. subst.
  split; reflexivity.
Qed.

(* Need a property stronger than injectivity because of f = (fun (x : Idx n) => x%n), injective
although (map f) does not conserve injectivity *)
Proposition map_conserve_injectivity :
  forall A B (n : nat) (f : ViewArray A -> ViewArray B),
    conserveInjectivity f ->
    conserveInjectivity (map f) (A := [[A;n]]).
Proof.
  intros. unfold conserveInjectivity in *. unfold map in *.
    intros. destruct x,y. 
    unfold isInjective in *. simpl in *.
    unfold partialApp in H1. 
Admitted.



(* Fixpoint non_empty_dimension (T : List nat) : Prop :=
  match T with
  | [] => True
  | h::tl => (h > 0) /\ (non_empty_dimension tl)
end.

Lemma non_empty_tuple_inhabited :
  forall d, non_empty_dimension d -> exists (_ : Tuple d), True.
Proof.
  induction d.
  - intros. simpl. exists I. apply I.
  - simpl. simpl in IHd. intros. destruct H. apply IHd in H0. destruct H0.
      exists (Id h 0 H, x). apply I.
Qed.


Proposition app_conserve_injectivity :
  forall T n (v : ViewArray [[T;n]]), non_empty_dimension T -> isInjective v -> forall i j, (partialApp v i) = (partialApp v j) -> i = j
.
Proof.
  unfold isInjective.
  intros T n v Hd H i j H0.
    unfold partialApp in H0.
    apply non_empty_tuple_inhabited in Hd. destruct Hd. 
    assert (forall x, (fun x : Tuple T => v (i, x)) x = (fun x : Tuple T => v (j, x)) x).
    { apply FunEquality. apply H0. }
    assert ((fun x : Tuple T => v (i, x)) x = (fun x : Tuple T => v (j, x)) x).
    apply H2.
    simpl in H3. apply H in H3. injection H3. trivial.
Qed.
*)
