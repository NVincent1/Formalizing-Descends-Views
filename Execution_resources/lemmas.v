
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
From Views.Execution_resources Require Import sets_of_threads.
Require Import PeanoNat.


Axiom excluded_middle :
(* The excluded middle would not be needed if proofs in this file were limited to 
the use case in this project, and not with a general type T, as it is relatively easy to prove
that for any naturals x and y, x = y \/ x <> y,
but it is not possible in a general case without excluded middle *)
  forall P,
  P \/ ~P
.

(** Properties of `cat` and `count` *)

Lemma cat_count :
  forall T l1 l2 (x : T) m n,
  count x l1 m -> count x l2 n -> count x (l1++l2) (m+n)
.
Proof.
  induction l1.
  - intros. inversion H. subst. apply H0.
  - intros. inversion H.
    + subst. apply IHl1 with (l2 := l2) (n := n) in H5.
    apply cons_eq.
    apply H5.
    apply H0.
    + subst. apply IHl1 with (l2 := l2) (n := n) in H5.
    apply cons_neq. apply H5. apply Hneq. apply H0.
Qed.

Lemma cat_count_rev :
  forall T l1 l2 (x : T) n,
  count x (l1++l2) n -> exists m m', count x l1 m /\ count x l2 m' /\ (m+m' = n)
.
Proof.
  induction l1.
  - intros. inversion H.
    + simpl in *. subst. exists 0,0. split. apply empty. split. apply empty. reflexivity.
    + simpl in *. subst. exists 0,(S n0). split. apply empty. split. apply H. reflexivity.
    + simpl in *. subst. exists 0,n. split. apply empty. split. apply H. reflexivity.
  - intros. inversion H.
    + simpl in *. subst. apply IHl1 in H4.
    destruct H4 as [m H4]. destruct H4 as [m' H4].
    destruct H4 as [H1 [H2 H3]].
    exists (S m),m'. split. apply cons_eq. apply H1. split. apply H2. simpl. rewrite H3. reflexivity.
    + simpl in *. subst. apply IHl1 in H4.
    destruct H4 as [m H4]. destruct H4 as [m' H4].
    destruct H4 as [H1 [H2 H3]].
    exists m,m'. split. apply cons_neq. apply H1. apply Hneq. split. apply H2. simpl. rewrite H3. reflexivity.
Qed.

Lemma count_reorder :
  forall T l1 l2 (y x : T) n,
  count x (l1++y::l2) n <-> count x (y::l1++l2) n
.
Proof.
  induction l1.
  - intros. split; intro.
    + inversion H.
        subst. simpl in *. apply H.
        subst. simpl in *. apply H.
    + inversion H.
      subst. simpl in *. apply H.
      subst. simpl in *. apply H.
  - intros. split; intro.
    + inversion H.
      * subst. apply IHl1 in H4.
      inversion H4; subst. apply cons_eq. apply cons_eq. apply H5.
      apply cons_neq. apply cons_eq. apply H5. apply Hneq.
      * subst. apply IHl1 in H4.
      inversion H4; subst. apply cons_eq. apply cons_neq. apply H5. apply Hneq.
      apply cons_neq. apply cons_neq. apply H5. apply Hneq. apply Hneq0.
    + inversion H.
      * subst. apply IHl1 in H4.
        inversion H4; subst.
        ++ destruct l1; inversion H2.
        ++ destruct l1; inversion H0; subst; simpl in *.
              apply cons_eq. apply H4.
              inversion H; subst. inversion H6; subst.
              apply cons_eq. apply cons_eq. apply H2.
              apply cons_neq. apply IHl1.
              apply cons_eq. apply H8. apply Hneq.
              exfalso. apply Hneq. reflexivity.
        ++ destruct l1; inversion H0; subst; simpl in *.
              apply cons_neq. apply cons_eq. apply H2. apply Hneq.
              inversion H; subst. inversion H6; subst.
              apply cons_eq. apply cons_neq. apply H2. apply Hneq.
              apply cons_neq. apply IHl1.
              apply cons_eq. apply H8. apply Hneq0.
              exfalso. apply Hneq0. reflexivity.
      * subst. apply IHl1 in H4.
        inversion H4; subst.
        ++ destruct l1; inversion H2.
        ++ destruct l1. simpl in *.
            inversion H0; subst.
            inversion H; subst. exfalso. apply Hneq. reflexivity.
            inversion H7; subst. apply cons_eq. apply cons_neq. apply H6. apply Hneq.
            exfalso. apply Hneq1. reflexivity.
            inversion H; subst.
            exfalso. apply Hneq. reflexivity.
            inversion H7; subst.
            apply cons_eq. apply IHl1.
            apply cons_neq. apply H5. apply Hneq0.
            apply cons_neq. apply IHl1.
            apply cons_neq. apply H8. apply Hneq0. apply Hneq1.
        ++ destruct l1; inversion H0; subst; simpl in *.
              apply cons_neq. apply cons_neq. apply H2. apply Hneq. apply Hneq0.
              inversion H; subst. exfalso. apply Hneq. reflexivity.
              inversion H; subst. inversion H8; subst.
              apply cons_eq. apply IHl1.
              apply cons_eq. apply H9.
              exfalso. apply Hneq1. reflexivity.
              inversion H8; subst.
              apply cons_eq. apply IHl1. apply cons_neq. apply H9.
              apply Hneq.
              apply cons_neq. apply IHl1. apply cons_neq. apply H9.
              apply Hneq. apply Hneq3.
Qed.

Lemma cat_empty :
  forall T (l : List T),
  l ++ [] = l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma cat_assoc :
  forall T (l1 l2 l3 : List T),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  induction l1.
  reflexivity.
  simpl. intros. rewrite IHl1. reflexivity.
Qed.

Proposition count_unicity :
  forall T (x : T) l m n,
  count x l m -> count x l n -> m = n.
Proof.
  induction l;
  intros.
  - inversion H. inversion H0. reflexivity.
  - inversion H; subst; inversion H0; subst.
    + assert (n0 = n1). apply IHl. apply H5. apply H3. subst. reflexivity.
    + exfalso. apply Hneq. reflexivity.
    + exfalso. apply Hneq. reflexivity.
    + apply IHl. apply H5. apply H6.
Qed.

Proposition count_exists :
  forall T (x : T) l,
  exists n, count x l n.
Proof.
  induction l.
  - exists 0. apply empty.
  - destruct IHl.
    assert (x = h \/ x <> h). apply excluded_middle.
    destruct H0.
      + subst. exists (S x0). apply cons_eq. apply H.
      + exists x0. apply cons_neq. apply H. apply H0.
Qed.

Lemma cons_cat :
  forall T (x:T) l,
    x::l = (x :: [])++l.
Proof.
  reflexivity.
Qed.

Proposition count_inverse :
  forall T l1 l2 (a : T) n,
  count a (l1 ++ l2) n ->
  count a (l2 ++ l1) n.
Proof.
  induction l2.
  - intros. rewrite cat_empty in H. apply H.
  - intros. simpl in *. apply count_reorder in H.
  inversion H; subst.
    apply cons_eq. apply IHl2. apply H4.
    apply cons_neq. apply IHl2. apply H4. apply Hneq.
Qed.

(** Properties of `zip` *)

Lemma zip_cons :
  forall T x (fi : nat -> T),
    zip (buildList x (fun i : nat => fi i :: [])) =
    buildList x (fun i : nat => fi i).
Proof.
  induction x.
  - reflexivity.
  - simpl. intros. rewrite IHx. reflexivity.
Qed.

Lemma zip_count :
  forall T (a : T) x (fi : nat -> T) n,
    count a (zip (buildList x (fun i : nat => fi i :: []))) n <->
    count a (buildList x (fun i : nat => fi i)) n.
Proof.
  intros. split; rewrite zip_cons; intro H; apply H.
Qed.

Lemma zip_cat :
  forall T (l1 l2 : List (List T)),
  zip (l1 ++ l2) = zip l1 ++ zip l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite <- cat_assoc. rewrite IHl1. reflexivity.
Qed.

(** Properties of `map` *)

Proposition map_cat :
  forall T T' l1 l2 (f : T -> T'),
  map f (l1++l2) = map f l1 ++ map f l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Proposition map_buildlist :
  forall T T' n (f : T -> T') g,
  map f (buildList n (fun i => g i)) = buildList n (fun i => f (g i)).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Proposition map_zip_buildlist :
  forall T T' n (f : T -> T') g,
  map f (zip (buildList n (fun i => g i))) = zip (buildList n (fun i => map f (g i))).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite map_cat. rewrite IHn. reflexivity.
Qed.

(** natural equality and its correctness *)

Fixpoint eqb (m n : nat) :=
  match m,n with
  | 0,0 => true
  | S m, S n => eqb m n
  | _,_ => false
end.

Proposition eqb_correct :
  forall m n, eqb m n = true -> m = n
.
Proof.
  induction m.
  - destruct n. reflexivity. intro. inversion H.
  - destruct n. intro. inversion H. intro. apply IHm in H. subst; reflexivity.
Qed.

Proposition eqb_correct_contra :
  forall m n, m <> n -> eqb m n = false
.
Proof.
  induction m.
  - destruct n. intro. exfalso. apply H. reflexivity. reflexivity.
  - destruct n. reflexivity. intro. apply IHm. intro. rewrite H0 in H. apply H. reflexivity.
Qed.

Proposition eqb_refl :
  forall n, eqb n n = true
.
Proof.
  induction n.
  - reflexivity.
  - apply IHn.
Qed.

Proposition leb_correct :
  (* Correctness of natural inequality *)
  forall a b,
  a <=? b = true -> a <= b.
Proof.
  induction a.
  - intros. apply le_0_n.
  - destruct b. intro H. inversion H.
    simpl. intro H. apply IHa in H. apply le_n_S. apply H.
Qed.

(** Sum of elements of a (multi-dimensional) vector *)

Fixpoint sum {n : nat} (v : Vector nat n) :=
  match n with
  | 0 => 0
  | S n => v n + sum v (n := n)
end.

(** Equality of vectors elements implies equality of their sum *)

Proposition vector_sum_eq :
  forall n (v1 v2 : Vector nat n),
  (forall i, i < n -> v1 i = v2 i) -> sum v1 = sum v2.
Proof.
  induction n.
  - reflexivity.
  - intros. simpl. assert (forall i : nat, i < n -> v1 i = v2 i).
    intros. apply le_S in H0. apply H in H0. apply H0.
    apply IHn in H0. rewrite H0.
    assert (v1 n = v2 n). apply H. apply le_n. rewrite H1.
    reflexivity.
Qed.

Proposition map_count_0 :
  forall A B (f : A -> B) l y, (forall x, f x = y -> count x l 0) -> count y (map f l) 0.
    induction l. intros. apply empty.
        intros. simpl. apply cons_neq. apply IHl.
        intros. apply H in H0. inversion H0. apply H5.
        intro. symmetry in H0. apply H in H0. inversion H0. apply Hneq. reflexivity.
Qed.

Proposition map_count_1 :
  forall A B (f : A -> B) X l y, f X = y -> count X l 1 -> (forall x, f x = y -> x = X \/ count x l 0) -> count y (map f l) 1.
    induction l.
      + intros. inversion H0.
      + intros. simpl. inversion H0.
        * rewrite H2 in *. rewrite <- H. apply cons_eq.
          assert (forall x, f x = y -> count x l 0). {
            intros. apply H1 in H7. destruct H7.
            - subst.  apply H4.
            - inversion H7. apply H12.
          } apply map_count_0 in H7. subst. apply H7.
        * apply IHl in H as H'. assert (f h <> y).
          intro. apply H1 in H7. destruct H7. symmetry in H7. apply Hneq in H7. apply H7.
          inversion H7. apply Hneq0. reflexivity.
          apply cons_neq. apply H'. symmetry. apply H7. apply H6.
          intros. apply H1 in H7. destruct H7. left. apply H7.
          right. inversion H7. apply H12.
Qed.



