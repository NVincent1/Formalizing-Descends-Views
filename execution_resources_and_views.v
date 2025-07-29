
Require Import PeanoNat.
From Views.Execution_resources Require Import Execution_resources.
From Views Require Import Views.
From Views Require Import utils.
From Views Require Import Proof.
From Views Require Import BoundedInt.


Fixpoint simplify_type (T : List nat) : List nat :=
  match T with
  | [] => []
  | 1::tl => simplify_type tl
  | h::tl => h::(simplify_type tl)
end.

Fixpoint simplify_view {T : List nat} : ViewArray T -> ViewArray (simplify_type T) :=
  (* remove 1-dimension layers *)
  match T with
  | [] => fun v => v
  | 1::tl => fun v => (simplify_view (v zero))
  | _::tl => fun v i => simplify_view (v i)
end.


Fixpoint check_aux {T : List nat} (e : execution_resource) : ViewArray T -> Prop  :=
  match e,T with
  | Collection n content, h::tl => fun (v : ViewArray (h::tl)) =>
        h = n /\ (forall i (H : i < h), check_aux (content i) (v (idx h i H)))
  | TensorCollection x y z content, hx::hy::hz::tl => fun (v : ViewArray (hx::hy::hz::tl)) =>
        hx = x /\ hy = y /\ hz = z /\
        (forall i j k (Hx : i < hx) (Hy : j < hy) (Hz : k < hz),
        check_aux (content i j k) (v (idx hx i Hx) (idx hy j Hy) (idx hz k Hz)))
  | thread i,_ => fun v => True
  | lthread i,_ => fun v => True
  | _,_ => fun v => False
end.

Definition check {T : List nat} (e : execution_resource) (v : ViewArray T) : Prop :=
  (* outputs a proposition that holds iff v[[e]] can be applied *)
  check_aux (simplify e) (simplify_view v)
.

Example example :
  forall k, k = 8 \/ k = 4 \/ k = 2 \/ k = 1 ->
  check (sub_selection (threads (Block (X 32))) 0 k _x) (view (group (8/k)) (identity_view (8/k*k))).
Proof. intros. repeat (destruct H as [H | H]); subst.
  simpl. unfold check. simpl.
  split. reflexivity. intros. apply I.
  simpl. unfold check. simpl.
  split. reflexivity. intros. apply I.
  simpl. unfold check. simpl.
  split. reflexivity. intros. apply I.
  simpl. unfold check. simpl.
  apply I.
Qed.
