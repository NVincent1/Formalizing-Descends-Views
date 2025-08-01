
From Views Require Import utils.
From Views Require Import BoundedInt.
From Views Require Import Views.
From Views Require Import Proof.
From Views Require Import Views_Lemmas.
Require Import PeanoNat.

Axiom FunEquality :
  forall A B (f : A -> B) (g : A -> B),
  f = g <-> forall x, f x = g x.

Example test_take_left :
  view (take_left 3) (identity_view 8) =
  fun x => match x with
  | idx _ 0 _ => 0
  | idx _ 1 _ => 1
  | idx _ 2 _ => 2
| _ => 0
end.
Proof.
  unfold take_left. unfold identity_view. unfold reverse.
  simpl. apply FunEquality. intro x.
  destruct x.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  inversion H. inversion H1. inversion H3. inversion H5.
Qed.

Example test_take_right :
  view (take_right 3) (identity_view 8) =
  fun x => match x with
  | idx _ 0 _ => 3
  | idx _ 1 _ => 4
  | idx _ 2 _ => 5
  | idx _ 3 _ => 6
  | idx _ 4 _ => 7
| _ => 0
end.
Proof.
  unfold take_right. unfold identity_view. unfold reverse.
  simpl. apply FunEquality. intro x.
  destruct x.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  destruct n. reflexivity.
  inversion H. inversion H1. inversion H3. inversion H5. inversion H7. inversion H9.
Qed.

Example test_select_range :
  view (select_range 3 5) (identity_view 8) =
  fun x => match x with
  | idx _ 0 _ => 3
  | idx _ 1 _ => 4
| _ => 0
end.
Proof.
  unfold select_range. unfold identity_view. unfold reverse.
  simpl. apply FunEquality. intro x.
  destruct x.
  destruct n. reflexivity.
  destruct n. reflexivity.
  inversion H. inversion H1. inversion H3.
Qed.

Example test_group :
  view (group 3) (identity_view (3*2)) = 
  fun x y => match (x,y) with 
  | (idx _ 0 _,idx _ 0 _) => 0 | (idx _ 0 _,idx _ 1 _) => 1 | (idx _ 0 _,idx _ 2 _) => 2
  | (idx _ 1 _,idx _ 0 _) => 3 | (idx _ 1 _,idx _ 1 _) => 4 | (idx _ 1 _,idx _ 2 _) => 5
| _ => 0
end.
Proof.
  simpl. unfold map. unfold identity_view. unfold group. unfold reverse. 
  apply FunEquality. intros. apply FunEquality. intro y. destruct x as [x Hx]. destruct y as [y Hy].
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  exfalso. inversion Hx. inversion H0. inversion H2.
Qed.

Example test_transpose :
  view transpose (view (group 3) (identity_view (3*2))) =
  fun x y => match (x,y) with
  | (idx _ 0 _,idx _ 0 _) => 0 | (idx _ 0 _,idx _ 1 _) => 3
  | (idx _ 1 _,idx _ 0 _) => 1 | (idx _ 1 _,idx _ 1 _) => 4
  | (idx _ 2 _,idx _ 0 _) => 2 | (idx _ 2 _,idx _ 1 _) => 5
| _ => 0
end.
Proof.
  simpl. unfold transpose. unfold identity_view. unfold group.
  apply FunEquality. intros. apply FunEquality. intro y. destruct x as [x Hx]. destruct y as [y Hy].
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2.
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2.
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2.
  exfalso. inversion Hx. inversion H0. inversion H2. inversion H4.
Qed.

Example test_map :
  (map (view reverse) (view (group 3) (identity_view (3*2)))) = 
  fun x y => match (x,y) with 
  | (idx _ 0 _,idx _ 0 _) => 2 | (idx _ 0 _,idx _ 1 _) => 1 | (idx _ 0 _,idx _ 2 _) => 0
  | (idx _ 1 _,idx _ 0 _) => 5 | (idx _ 1 _,idx _ 1 _) => 4 | (idx _ 1 _,idx _ 2 _) => 3
| _ => 0
end.
Proof.
  simpl. unfold map. unfold identity_view. unfold group. unfold reverse. 
  apply FunEquality. intros. apply FunEquality. intro y. destruct x as [x Hx]. destruct y as [y Hy].
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  destruct x. simpl. destruct y. reflexivity. destruct y. reflexivity. destruct y. reflexivity. exfalso. inversion Hy. inversion H0. inversion H2. inversion H4.
  exfalso. inversion Hx. inversion H0. inversion H2.
Qed.

(* Example of a fonction that returns an injective array, which does not verify the property we want to have for views *)
Definition index_identity {T : List nat} {n : nat} (v : ViewArray [[T;n]]) : ViewArray [[;n]] :=
  fun i => to_nat i.

Example index_identity_does_not_preserve_injectivity :
  ~ (forall T n, preserve_Injectivity index_identity (A := (n::T))).
Proof.
  intro H.
  unfold preserve_Injectivity in H.
  assert (0 < 2). apply le_n_S. apply le_0_n.
  assert (1 < 2). apply le_n_S. apply le_n.
  assert (Injective (view (group 2) (identity_view (2*2)))).
    assert (Injective (identity_view (2*2)) -> Injective (view (group 2) (identity_view (2 * 2)))).
    apply preserve_Injectivity_implies_preserving_view_injectivity. apply group_preserves_injectivity.
    apply H2. apply identity_view_injective.
  assert (((idx 2 1 H1), (idx 2 0 H0,I)) = ((idx 2 0 H0), (idx 2 0 H0,I))).
  apply H with (v := (view (group 2) (identity_view (2*2)))) 
      (i := (idx 2 1 H1))
      (x := (idx 2 0 H0,I))
      (j := (idx 2 0 H0))
      (y := (idx 2 0 H0,I))
  . intros. apply H2. simpl. apply H3. reflexivity.
  inversion H3.
Qed.

(* Proving that zip and group are inverses of each other *)
Proposition flatten_group_inverse :
  forall T m n (v : ViewArray (n::m:: T)), view (group m) (view (flatten m) v) = v.
Proof.
  intros.
  unfold flatten. simpl. unfold group. simpl. unfold view. simpl.
  unfold partapp.
  simpl. apply FunEquality. intro x. apply FunEquality. intro x'.
  assert (uncurry (curry_totalApp
     (uncurry (curry_totalApp
           (v (idx n ((to_nat x' + m * to_nat x) / m)
                (flattenBounded2 (i := idx (m*n) (to_nat x' + m * to_nat x) groupBounded)))
              (idx m ((to_nat x' + m * to_nat x) mod m) 
                (flattenBounded1 (i := idx (m*n) (to_nat x' + m * to_nat x) groupBounded)))))))
              = v x x').
  rewrite curry_uncurry_inverse.
  rewrite curry_uncurry_inverse.
  assert ((idx n ((to_nat x' + m * to_nat x) / m)
                (flattenBounded2 (i := idx (m*n) (to_nat x' + m * to_nat x) groupBounded))) = x). {
    apply to_nat_injective. simpl.
    rewrite Nat.mul_comm. rewrite Nat.div_add. rewrite Nat.div_small. reflexivity.
    apply BoundedInt. intro. subst. inversion x'. inversion H.
  } rewrite H.
  assert ((idx m ((to_nat x' + m * to_nat x) mod m)
                (flattenBounded1 (i := idx (m*n) (to_nat x' + m * to_nat x) groupBounded))) = x'). {
    apply to_nat_injective. simpl.
    rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity.
    apply BoundedInt.
  } rewrite H0. reflexivity. apply H.
Qed.

Proposition group_flatten_inverse :
  forall T m n (v : ViewArray (m*n:: T)), view (flatten m) (view (group m) v) = v.
Proof.
  intros.
  unfold flatten. simpl. unfold group. simpl. unfold view. simpl.
  unfold partapp.
  simpl. apply FunEquality. intro x.
  assert (uncurry (curry_totalApp
     (uncurry (curry_totalApp (v (idx (m * n) (to_nat x mod m + m * (to_nat x / m)) 
          (groupBounded (i := idx m (to_nat x mod m) flattenBounded1) (j := idx n (to_nat x / m) flattenBounded2)))))))
        = v x).
  rewrite curry_uncurry_inverse.
  rewrite curry_uncurry_inverse.
  assert ((idx (m * n) (to_nat x mod m + m * (to_nat x / m)) 
          (groupBounded (i := idx m (to_nat x mod m) flattenBounded1) (j := idx n (to_nat x / m) flattenBounded2))) = x).
    apply to_nat_injective. simpl.
    rewrite Nat.Div0.div_mod with (b := m).
    rewrite Nat.add_comm. reflexivity.
  rewrite H. reflexivity. apply H.
Qed.


