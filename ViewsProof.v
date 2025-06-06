
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
  | n::[] => Idx n
  | n::tl => Idx n * (Tuple tl)
end.

Definition ViewArray (d : List nat) : Type :=
  match d with
  | [] => nat
  | d =>  Tuple d -> nat
end.

Notation "[[ T ; n ]]" := (ViewArray (n::T)).
Notation "[[; n ]]" := (ViewArray (n::(Nil nat))).
Notation "[[ [[ T ; m ]] ; n ]]" := (ViewArray (n::m::T)).
Notation "[[ [[ ; m ]] ; n ]]" := (ViewArray (n::m::[])).

Definition to_view (n : nat) : [[; n]] :=
  fun i => to_nat i.


Definition reverse {T : List nat} {n : nat}  : [[T;n]] -> [[T;n]] :=
  match T with
  | [] => fun (v : [[;n]]) => fun (i : Tuple (n::[])) =>
      v (to_Idx n (n - 1 - (to_nat i)) reverseProof)
  | T => fun (v : [[T;n]]) => fun (i : Tuple (n::T)) =>
      match i with | (i,j) =>
      v (to_Idx n (n - 1 - (to_nat i)) reverseProof, j)
end
end.

Definition select  {T :List nat} {l : nat} (a : nat) (b : nat) : [[T;b + l]] -> [[T;b - a]] :=
  match T with
  | [] => fun (v : [[;b + l]]) => fun (i : Tuple ((b-a)::[])) =>
      v (to_Idx (b+l) (a + to_nat i) selectProof)
  | T => fun (v : [[T;b + l]]) => fun (i : Tuple ((b-a)::T)) =>
      match i with | (i,j) =>
      v (to_Idx (b+l) (a + to_nat i) selectProof, j)
end
end.

Definition group {T : List nat} (m : nat) (n : nat) : [[T ; m*n]] -> [[ [[T;m]] ; n]] :=
  match T with
  | [] => fun (v : [[;m*n]]) => fun (i : Tuple (n::m::[])) =>
      match i with | (i,j) =>
      v (to_Idx (m*n) (to_nat j + m*(to_nat i)) groupProof)
  end
  | T => fun (v : [[T;m*n]]) => fun (i : Tuple (n::m::T)) =>
      match i with | (i,(j,k)) =>
      v (to_Idx (m*n) (to_nat j + m*(to_nat i)) groupProof,k)
  end
end.

Definition transpose {T : List nat} {m : nat} {n : nat} : [[ [[T;m]] ; n]] -> [[ [[T;n]] ; m]] :=
  match T with
  | [] => fun (v : [[ [[ ;m]] ; n]]) => fun (i : Tuple (m::n::[])) =>
    match i with | (i,j) => v (j,i)
  end
  | T => fun (v : [[ [[T;m]] ; n]]) => fun (i : Tuple (m::n::T)) =>
    match i with | (i,(j,k)) => v (j,(i,k))
  end
end.

Definition partialApp {T : List nat} {n : nat} : [[T;n]] -> Idx n -> (ViewArray T) :=
  match T with
  | [] => fun (v : [[;n]]) i => (v i)
  | T => fun (v : [[T;n]]) i x => v (i,x)
end.

Definition map {A : List nat} {B : List nat} {n : nat} : (ViewArray A -> ViewArray B)  -> [[A;n]] -> [[B;n]] :=
  match B with
  | [] => fun f (v : [[A;n]]) (i : Tuple (n::[])) => (f (partialApp v i))
  | B => fun f (v : [[A;n]]) (i : Tuple (n::B)) => match i with | (i,j) => (f (partialApp v i)) j
  end
end.


Definition isInjective {T : List nat} : ViewArray T -> Prop :=
  match T with 
  | [] => fun (f : ViewArray [])  => True
  | T => fun (f : ViewArray T) => forall (i : Tuple T) (j : Tuple T), f i = f j -> i = j
end.

Proposition to_view_is_injective :
  forall (n : nat), isInjective (to_view n).
Proof.
  unfold isInjective. unfold to_view. intros. apply to_nat_injective in H. apply H.
Qed.

Proposition reverse_conserve_injectivity :
  forall (T:List nat) (n : nat) (v : [[T;n]]), isInjective v -> isInjective (reverse v).
Proof.
    destruct T.
    - unfold isInjective. intros. unfold reverse in H0. apply H in H0.
      inversion H0. apply sub_injective with (c := n - 1) in H2. apply to_nat_injective in H2. apply H2.
      + destruct n. assert (to_nat i < 0). apply BoundedInt. inversion H1. simpl. rewrite Nat.sub_0_r.
      assert (S (to_nat i) <= S n). apply BoundedInt. apply le_S_n in H1. apply H1. 
      + destruct n. assert (to_nat j < 0). apply BoundedInt. inversion H1. simpl. rewrite Nat.sub_0_r.
      assert (S (to_nat j) <= S n). apply BoundedInt. apply le_S_n in H1. apply H1.
    - unfold isInjective. intros. unfold reverse in H0. destruct i as [i xi]; destruct j as [j xj]. apply H in H0.
      inversion H0. apply sub_injective with (c := n - 1) in H2. apply to_nat_injective in H2. rewrite H2. reflexivity.
      + destruct n. assert (to_nat i < 0). apply BoundedInt. inversion H1. simpl. rewrite Nat.sub_0_r.
      assert (S (to_nat i) <= S n). apply BoundedInt. apply le_S_n in H1. apply H1. 
      + destruct n. assert (to_nat j < 0). apply BoundedInt. inversion H1. simpl. rewrite Nat.sub_0_r.
      assert (S (to_nat j) <= S n). apply BoundedInt. apply le_S_n in H1. apply H1.
Qed.

Proposition select_conserve_injectivity :
  forall T a b k (v : [[T;b+k]]), isInjective v -> isInjective (select a b v).
Proof.
  unfold isInjective.
  unfold select.
  intros.
  destruct T.
  - apply H in H0. inversion H0. apply add_injective in H2. apply to_nat_injective in H2. apply H2.
  - destruct i as [i xi]; destruct j as [j xj]. apply H in H0. inversion H0. apply add_injective in H2.
  apply to_nat_injective in H2. rewrite H2. reflexivity.
Qed.

Proposition group_conserve_injectivity:
  forall T m n (v : [[T;m*n]]), isInjective v -> isInjective (group m n v).
Proof.
  unfold isInjective. unfold group.
  intros.
  destruct T; destruct i as [i1 j1]; destruct j as [i2 j2].
  - apply H in H0. inversion H0. assert ((to_nat j1,to_nat i1) = (to_nat j2,to_nat i2)). apply projection_injective with (k := m). apply BoundedInt. apply BoundedInt. apply H2.
  injection H1. intros. apply to_nat_injective in H3. rewrite H3.  apply to_nat_injective in H4. rewrite H4. reflexivity.
  - destruct j1 as [j1 x1]; destruct j2 as [j2 x2]. apply H in H0. inversion H0. assert ((to_nat j1,to_nat i1) = (to_nat j2,to_nat i2)). apply projection_injective with (k := m). apply BoundedInt. apply BoundedInt. apply H2.
  injection H1. intros. apply to_nat_injective in H4. rewrite H4.  apply to_nat_injective in H5. rewrite H5. reflexivity.
Qed.

Proposition transpose_conserve_injectivity :
  forall T m n (v : [[[[T;m]];n]]), isInjective v -> isInjective (transpose v).
Proof.
  unfold isInjective. unfold transpose.
  intros.
  destruct T; destruct i as [i1 j1]; destruct j as [i2 j2].
  - apply H in H0. injection H0. intros. subst. reflexivity.
  - destruct j1 as [j1 x1]; destruct j2 as [j2 x2]. apply H in H0. injection H0. intros. subst. reflexivity.
Qed.

Fixpoint non_empty_dimension (T : List nat) : Prop :=
  match T with
  | [] => True
  | h::tl => (h > 0) /\ (non_empty_dimension tl)
end.

Lemma non_empty_tuple_inhabited :
  forall d, non_empty_dimension d -> exists (_ : Tuple d), True.
Proof.
  induction d.
  - intros. simpl. exists I. apply I.
  - destruct d.
    + simpl. intros. destruct H. exists (Id h 0 H). apply I.
    + simpl. simpl in IHd. intros. destruct H. apply IHd in H0. destruct H0.
      exists (Id h 0 H, x). apply I.
Qed.


Proposition app_conserve_injectivity :
  forall T n (v : [[T;n]]), non_empty_dimension T -> isInjective v -> forall i j, (partialApp v i) = (partialApp v j) -> i = j
.
Proof.
  unfold isInjective.
  intros T n v Hd H i j H0.
  destruct T.
  - apply H in H0. apply H0.
  - unfold partialApp in H0.
    apply non_empty_tuple_inhabited in Hd. destruct Hd. 
    assert (forall x, (fun x : Tuple (h :: T) => v (i, x)) x = (fun x : Tuple (h :: T) => v (j, x)) x).
    { apply FunEquality. apply H0. }
    assert ((fun x : Tuple (h :: T) => v (i, x)) x = (fun x : Tuple (h :: T) => v (j, x)) x).
    apply H2.
    simpl in H3. apply H in H3. injection H3. trivial.
Qed.

Definition funInjective {A : List nat} {B : List nat} : (ViewArray A -> ViewArray B) -> Prop :=
  match B with
  | [] => fun (f : ViewArray A -> ViewArray []) => forall v v', f v = f v' -> v = v'
  | B => fun (f : ViewArray A -> ViewArray B) =>
  forall n (v:[[A;n]]) a b x y, isInjective v -> f (partialApp v a) x = f (partialApp v b) y -> x = y /\ a = b
end.

  

Proposition map_conserve_injectivity :
  forall (A : List nat) (B : List nat) (f : ViewArray A -> ViewArray B) (n : nat) (v : [[A;n]]),
    non_empty_dimension A ->
    (forall v, isInjective v -> isInjective (f v)) -> funInjective f ->
    isInjective v -> isInjective (map f v).
Proof.
  intros. unfold isInjective in *. unfold map in *. unfold funInjective in *.
  destruct A.
  - destruct B.
    + simpl in *.
    intros. apply H1 in H3. apply H2 in H3. apply H3.
    + intros. destruct i; destruct j. simpl in H3. simpl in H1. apply H1 in H3. destruct H3. subst. reflexivity.
    apply H2.
  - destruct B. 
    + intros. destruct i; destruct j. apply H1 in H3. simpl in H3.
    assert (forall x, v (Id n n0 H4, x) = v (Id n n1 H5, x)). apply FunEquality.
    apply H3. apply non_empty_tuple_inhabited in H. destruct H.
    assert (v (Id n n0 H4, x) = v (Id n n1 H5, x)). apply H6.
    apply H2 in H7. injection H7. intros. subst. apply unif_Idx.
    + intros. destruct i; destruct j. simpl in H3. simpl in H1. apply H1 in H3.
    destruct H3. subst. reflexivity.
    apply H2.
Qed.

Proposition reverse_is_ok :
  forall T n, funInjective reverse (A := n::T) (B := n::T).
Proof.
  intros. unfold funInjective. unfold partialApp. intros.
  destruct T.
  - apply H in H0. inversion H0.
    apply sub_injective with (c := n - 1) in H3. apply to_nat_injective in H3. split. apply H3. reflexivity.
    destruct n. destruct x. inversion H1. simpl. rewrite Nat.sub_0_r. destruct x. simpl. apply le_S_n. apply H1.
    destruct n. destruct y. inversion H1. simpl. rewrite Nat.sub_0_r. destruct y. simpl. apply le_S_n. apply H1.
  - 


