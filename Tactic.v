
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
Require Import PeanoNat.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
From Ltac2 Require Import Control.
From Ltac2 Require Import Std.

(** TODO : rename variables to decrease the risk of them being already introduced *)

Ltac2 rec introductions () :=
  (* introduces all variables and unfolds the definition *)
  match! goal with
  | [ h:_ |- ?g ] => match! g with
                    | preserve_Injectivity ?f => unfold preserve_Injectivity; intros set_C view_v H_v_inj index_i index_j index_x index_y Hypthesis
                    | _ => intro; introductions ()
                    end
  | [ |- _ ] => intro; introductions ()
end.



Ltac2 remember_destruction () :=
  (* detruct a tuple and remember it as a new variable (except for empty tuples) *)
  match! reverse goal with
  | [ h:Tuple [] |- _ ] => let h' := Control.hyp h in destruct $h'
  | [ h:Tuple _ |- _ ] => let h' := Control.hyp h in remember $h'; destruct $h'
end.

Ltac2 destruction () :=
  (* destruct the oldest tuple hypothesis *)
  match! reverse goal with
  | [ h:Tuple [] |- _ ] => let h' := Control.hyp h in destruct $h'
  | [ h:Tuple _ |- _ ] => let h' := Control.hyp h in destruct $h'
end.

Ltac2 subst2 () :=
  (* subst without removing the hypotheses *)
  repeat (match! goal with
  | [ heq:(_ = _), h:_ |- _] => let h' := Control.hyp heq in rewrite $h' in $h
end).

Ltac2 applyHinj (f:constr) :=
  (* use the injectivity hypothesis *)
   match! goal with
  | [ h1 : Injective ?v, hx:(?t1 = (?x,?tx)), hy:(?t2 = (?y,?ty)), hi:(?t3 = (?i,?ti)), j:(?t4 = (?j,?tj)), h : nat, c : List nat, v : ViewArray _, h2 : _ |- _] => let h1' := Control.hyp h1 in let h2' := Control.hyp h2 in
  let h := Control.hyp h in let c := Control.hyp c in
  assert (Hypothesis_equality : curry_totalApp (curry_partialApp $v (A := ($h::$c)) ($i,$ti)) ($f ($x,$tx)) =
          curry_totalApp (curry_partialApp $v (A := ($h::$c)) ($j,$tj)) ($f ($y,$ty))
        -> (($i,$ti),($f ($x,$tx))) = (($j,$tj),($f ($y,$ty))));
  try (apply injectivity_decomposition; apply $h1');
  apply &Hypothesis_equality in $h2
   | [ h1 : Injective ?v, hx:(?t1 = (?x,?tx)), hy:(?t2 = (?y,?ty)), h2 : _ |- _ ] => let h1' := Control.hyp h1 in let h2' := Control.hyp h2 in
  unfold Injective in *;
  apply $h1' with (x := $f ($x,$tx)) (y := $f ($y,$ty)) in $h2
end.


Ltac2 reordering_autoProof1 (f:constr) (fid:ident) (dim : int):=
  introductions ();
  remember_destruction ();
  do dim (destruction ());
  remember_destruction ();
  do dim (destruction ());
  match! goal with
  | [ h:List nat |- _ ] => let h' := Control.hyp h in destruct $h'
  end;
  enter (fun () =>
    remember_destruction ();
    remember_destruction ();
    subst2 ()
  ).


Ltac2 reordering_autoProof2 (f:constr) (fid:ident) (dim : int):=
  enter (fun () =>
    (applyHinj (f));
    let f' := VarRef (fid) in
    unfold $f' in Hypthesis;
    inversion Hypthesis;
    subst
  ).


Ltac2 reordering_autoProof (f:constr) (fid:ident) (dim : int):=
(* Semi-Automatic proof of correctness for reordering functions :
  takes as inputs :
  - a hint function, the reordering function, given as constr and ident
  - the expected number of dimension (minus one) of the input viewArray
  (cf. the examples in `Examples_automation.v`)
  Note : it will only work with simple enough functions (when no case disjunction is needed)
*)
  reordering_autoProof1 f fid dim;
  reordering_autoProof2 f fid dim.

Definition selectProof {n : nat} {m : nat} {i : Idx n} (H : m > 0):
  m*(to_nat i) < m*n.
Proof.
Admitted.

Definition select {T : List nat} {n : nat} (m : nat) (H : m > 0) (v : ViewArray[[T;m*n]]) : ViewArray[[T;n]] :=
  fun i => v (idx (m*n) (m*(to_nat i)) (selectProof H)).

Proposition test : forall T n m (H : m > 0), preserve_Injectivity (select m H) (A := (m*n::T)).
Proof.
  intros T n m H'.
  set (function := fun (x : Tuple (n::T)) => match x with | (i,tx) => (idx (m*n) (m*(to_nat i)) (selectProof H'),tx) end).
  reordering_autoProof ('function) (@function) 0.
  apply Nat.mul_cancel_l in H0. apply to_nat_injective in H0. subst. reflexivity ().
  intro. subst. inversion H'.
  apply Nat.mul_cancel_l in H2. apply to_nat_injective in H2. subst. reflexivity ().
  intro. subst. inversion H'.
Qed.


