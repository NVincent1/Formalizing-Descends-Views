
From Views Require Import Lemmas.
From Views Require Import utils.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsLemmas.
From Views Require Import ViewsProof.
Require Import PeanoNat.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
From Ltac2 Require Import Control.
From Ltac2 Require Import Std.

(** Importing LTac2 is needed in order to use the tactics provided in this file *)

Ltac2 destruction () :=
  (* destruct the oldest tuple hypothesis *)
  match! reverse goal with
  | [ h:Tuple [] |- _ ] => let h' := Control.hyp h in destruct $h'
  | [ h:Tuple _ |- _ ] => let h' := Control.hyp h in destruct $h'
end.


Ltac2 reordering_autoProof (dim : int):=
(* Semi-Automatic proof of correctness for reordering functions :
  takes as inputs :
  - a hint function, the reordering function, given as constr and ident
  - the expected number of dimension (minus one) of the input viewArray
  (cf. the examples in `Examples_automation.v`)
  Note : it will only work with simple enough functions (e.g. when no case disjunction is needed)
  for more complex functions you will have to use `auto_destruct`
  as well as `auto_apply` after disjuncting the cases (cf. the transposition example in `Examples_automation.v`
*)
  apply injective_function_preserve_injectivity;
  intros x y H;
  do dim (destruction ());
  do dim (destruction ());
  inversion H;
  subst.



