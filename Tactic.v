
From Views Require Import Lemmas.
From Views Require Import BoundedInt.
From Views Require Import ViewFunctions.
From Views Require Import ViewsProof.
Require Import PeanoNat.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
From Ltac2 Require Import Control.
From Ltac2 Require Import Std.


Ltac2 rec introductions () :=
  (* introduces all variables and unfolds the definition *)
  match! goal with
  | [ h:_ |- ?g ] => match! g with
                    | preserve_Injectivity ?f => unfold preserve_Injectivity; intros C v Hinj i j x y H
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
  | [ h1 : Injective ?v, hx:(?t1 = (?x,?tx)), hy:(?t2 = (?y,?ty)), hi:(?t3 = (?i,?ti)), j:(?t4 = (?j,?tj)), h2 : _ |- _ ] => let h1' := Control.hyp h1 in let h2' := Control.hyp h2 in
  assert (Heq : curry_totalApp (curry_partialApp &v (A := (&h::&C)) ($i,$ti)) ($f ($x,$tx)) =
          curry_totalApp (curry_partialApp &v (A := (&h::&C)) ($j,$tj)) ($f ($y,$ty))
        -> (($i,$ti),($f ($x,$tx))) = (($j,$tj),($f ($y,$ty))));
  try (apply injectivity_decomposition; apply $h1');
  apply &Heq in $h2
   | [ h1 : Injective ?v, hx:(?t1 = (?x,?tx)), hy:(?t2 = (?y,?ty)), h2 : _ |- _ ] => let h1' := Control.hyp h1 in let h2' := Control.hyp h2 in
  unfold Injective in *;
  apply $h1' with (x := $f ($x,$tx)) (y := $f ($y,$ty)) in $h2
end.


Ltac2 reordering_autoProof (f:constr) (fid:ident) (dim : int):=
(* Automatic proof of correctness for reordering functions :
  takes as inputs :
  - a hint function, the reordering function, given as constr and ident
  - the expected number of dimension of the input viewArray
  (cf. the examples in `Test.v`)
*)
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
    subst2 ();
    (applyHinj (f));
    let f' := VarRef (fid) in
    unfold $f' in H;
    inversion H;
    subst
  ).


