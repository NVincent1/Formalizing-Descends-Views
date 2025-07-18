
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
Require Import PeanoNat.


Fixpoint thread_set_1z {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => f (m x y z) ++ (thread_set_1z (S x) (S y) z f m)
  | _ => fun _ => []
end.


Fixpoint thread_set_1y {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => f (m x y z) ++ (thread_set_1y (S x) y (S z) f m)
  | _ => fun _ => []
end.

Fixpoint thread_set_2yz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => thread_set_1z (S x) (S y) (S z) f m  ++ (thread_set_2yz (S x) y (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_2xz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => thread_set_1z (S x) (S y) (S z) f m  ++ (thread_set_2xz x (S y) (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_2xy {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => thread_set_1y (S x) (S y) (S z) f m  ++ (thread_set_2xy x (S y) (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_3xyz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
         fun m => thread_set_2yz (S x) (S y) (S z) f m ++ (thread_set_3xyz x (S y) (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_3yxz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
         fun m => thread_set_2xz (S x) (S y) (S z) f m ++ (thread_set_3yxz (S x) y (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_3zxy {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
         fun m => thread_set_2xy (S x) (S y) (S z) f m ++ (thread_set_3zxy (S x) (S y) z f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set' (e : execution_resource) : List ThreadId_t :=
  match e with
  | Collection n v => zip (buildList n (fun i => thread_set' (v i)))
  | grid (x,y,z) (x',y',z') g => thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) g
  | block (x,y,z) _ b => thread_set_3xyz x y z (fun x => x :: []) b
  | lthread i => i::[]
  | _ => []
end.

(** TODO : add physical address translation of blocks, grids and lthreads *)
Fixpoint physical_thread_set (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : List PhysicalId_t :=
  match e with
  | Collection n v => zip (buildList n (fun i => physical_thread_set (v i) f))
  | thread i => i::[]
  | warp w => buildList Warp_size (fun i => w i)
  | _ => []
end.


Inductive count {T : Type} : T -> List T -> nat -> Prop :=
  | empty (x : T) : count x [] 0
  | cons_eq (x : T) (tl : List T) {n : nat} (H : count x tl n) : count x (x::tl) (S n)
  | cons_neq (x : T) (y : T) (tl : List T) {n : nat} (H : count x tl n) (Hneq : x <> y) : count x (y::tl) n
.

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

Axiom excluded_middle :
  forall P,
  P \/ ~P
.

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

Proposition count_impl_equiv :
  forall T (x : T) l1 l2,
  (forall n, count x l1 n -> count x l2 n) ->
  forall n, count x l2 n -> count x l1 n.
Proof.
  intros. assert (exists m, count x l1 m). apply count_exists.
  destruct H1. apply H in H1 as H2. apply count_unicity with (m := x0) in H0. subst. apply H1.
  apply H2.
Qed.

Proposition leb_correct :
  forall a b,
  a <=? b = true -> a <= b.
Proof.
  induction a.
  - intros. apply le_0_n.
  - destruct b. intro H. inversion H.
    simpl. intro H. apply IHa in H. apply le_n_S. apply H.
Qed.

Proposition count_reorder_2 :
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
