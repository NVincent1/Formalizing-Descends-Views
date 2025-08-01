
From Views Require Import utils.
Require Import PeanoNat.

Definition Warp_size : nat.
Proof. apply 0. Qed.

(* As Rocq has performance issues with larger examples,
the size of warps is set to 8 instead of 32 *)
Axiom Warp_size_value_8 :
  Warp_size = 8.


Definition shape : Type := nat * nat * nat.


Definition XYZ (x y z : nat) := (x,y,z).
Definition XY (x y : nat) := (x,y,1).
Definition XZ (x z : nat) := (x,1,z).
Definition YZ (y z : nat) := (1,y,z).
Definition X (x : nat) := (x,1,1).
Definition Y (y : nat) := (1,y,1).
Definition Z (z : nat) := (1,1,z).

Definition Tensor (T : Type) (shp : shape) : Type :=
  match shp with | (x,y,z) => nat -> nat -> nat -> T
end.

Definition Vector (T : Type) (n : nat) : Type :=
  nat -> T
.

Definition PhysicalId_t : Type := nat.
Definition LogicalId_t : Type := nat*nat*nat.
Definition ThreadId_t : Type := LogicalId_t*LogicalId_t.

Definition Thread_t : Type := LogicalId_t * LogicalId_t.
Definition PhysThread_t : Type := PhysicalId_t.
Definition Warp_t : Type := Vector PhysThread_t Warp_size.
Definition Block_t (shp : shape) : Type :=
      match shp with | (x,y,z) => Tensor Thread_t (x, y, z) end.
Definition Grid_t (shp : shape) (shp' : shape) : Type :=
      match shp with | (x,y,z) => Tensor (Block_t shp') (x, y, z) end.

Inductive execution_resource : Type :=
  | thread (t : PhysThread_t)
  | lthread (t : ThreadId_t)
  | warp (w : Warp_t)
  | block (shp : shape) (id : LogicalId_t) (b : Block_t shp)
  | grid (shp : shape) (shp' : shape) (g : Grid_t shp shp')
  | Collection (n : nat) (content : Vector execution_resource n)
  | TensorCollection (x y z : nat) (content : Tensor execution_resource (x,y,z))
    (* Used to represent a 3 dimensional collection e of execution resources
    on which we can apply e.forall(d) or e[l,r]d *)
  | Error
.


Definition build_block (shp : shape) (id : LogicalId_t) : Block_t shp :=
  match shp,id with
  | (x,y,z),(id_x,id_y,id_z) => fun i j k => ((id_x,id_y,id_z),(i,j,k))
end.

Definition build_grid (shp : shape) (shp' : shape) : Grid_t shp shp' :=
  match shp with
  | (x,y,z) => fun i j k => (build_block shp' (i,j,k))
end.

Definition build_warp (id : nat) : Warp_t :=
  fun i => (Warp_size*id) + i
.

Definition Thread (id : PhysicalId_t) := thread id.
Definition LThread (id : ThreadId_t) := lthread id.
Definition Warp (id : PhysicalId_t) := warp (build_warp id).
Definition Block (shp : shape) := block shp (0,0,0) (build_block shp (0,0,0)).
Definition Block' (shp : shape) (id : LogicalId_t) := block shp id (build_block shp id).
Definition Grid (shp : shape) (shp' : shape) := grid shp shp' (build_grid shp shp').

Inductive dimension :=
  | _x | _y | _z
.

Definition index_mapping := ThreadId_t -> PhysicalId_t.

Fixpoint build_collection (n : nat) (l : nat) (v : Vector execution_resource l) : execution_resource :=
  match n with
  | 0 => Collection l v
  | S n => match (v n) with
           | Error => Error
           | _ => build_collection n l v
           end
end.

Fixpoint leb (x : nat) (y : nat) : bool :=
  match x,y with
  | 0,_ => true
  | _,0 => false
  | S x, S y => (leb x y)
end.

Notation "x <=? y" := (leb x y).

Fixpoint for_all (e : execution_resource) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun i => for_all (v i) d)
  | TensorCollection x y z v, _x => Collection x (fun i => TensorCollection 1 y z (fun _ j k => v i j k))
  | TensorCollection x y z v, _y => Collection y (fun j => TensorCollection x 1 z (fun i _ k => v i j k))
  | TensorCollection x y z v, _z => Collection z (fun k => TensorCollection x y 1 (fun i j _ => v i j k))
  | _,_ => Error
end.

Definition assert (cond : bool) (success : execution_resource) : execution_resource :=
  if cond then success else Error.

Fixpoint sub_selection (e : execution_resource) (l : nat) (r : nat) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => sub_selection (v x) l r d)
  | TensorCollection x y z v, _x => assert (r <=? x) (Collection (r-l) (fun i => TensorCollection 1 y z (fun _ j k => v (i+l) j k)))
  | TensorCollection x y z v, _y => assert (r <=? y) (Collection (r-l) (fun j => TensorCollection x 1 z (fun i _ k => v i (j+l) k)))
  | TensorCollection x y z v, _z => assert (r <=? z) (Collection (r-l) (fun k => TensorCollection x y 1 (fun i j _ => v i j (k+l))))
  | _,_ => Error
end.

Inductive Nested_List (T : Type) : Type :=
  | Elt (x : T)
  | Nest (l : List (Nested_List T))
.

Fixpoint to_list (e : execution_resource) : Nested_List execution_resource :=
  (* Transform collections into list for better readability of the examples *)
  match e with
  | Collection n v => Nest _ (rev (buildList n (fun i => to_list (v i))))
  | TensorCollection x y z v => Nest _ (rev (buildList z (fun k => 
                                Nest _ (rev (buildList y (fun j =>
                                Nest _ (rev (buildList x (fun i => to_list (v i j k))))))))))
  | _ => Elt _ e
end.

Notation "[ l ]" := (Nest _ l).
Notation "@ x" := (Elt _ x) (at level 20).

Fixpoint next_multiple_aux (n : nat) (m : nat) :=
  match n with
  | 0 => 0
  | S n => match (S n mod m) with
           | 0 => S n
           | _ => next_multiple_aux n m
end
end.

Definition next_multiple (n : nat) (m : nat) :=
  match (n mod m) with
  | 0 => n
  | _ => next_multiple_aux (n + m) m
end.

Definition get_physical_id (shp : shape) (shp' : shape) : index_mapping :=
  fun id =>
  match shp,shp',id with
  | (x,y,z),(x',y',z'),((i,j,k),(i',j',k')) =>
    let s := next_multiple (x' * y' * z') Warp_size in
    i*s+j*x*s + k*y*z*s + i' + x'*j' + x'*y'*k'
end.

Definition warp_aux (shp : shape) (id : shape) (b : Block_t shp) (f : index_mapping) :=
  match shp,id with
  | (x,y,z),(idx,idy,idz) => TensorCollection ((next_multiple (x*y*z) Warp_size)/Warp_size) 1 1
                               (fun i j k =>  warp (fun i' => f ((idx,idy,idz),(i*Warp_size+i',j,k))))
end.

Fixpoint warps (e : execution_resource) (f : index_mapping) : execution_resource :=
  (* e.warps
  f is a function translating logical indices to physical indices *)
  match e with
  | Collection n v => Collection n (fun x => warps (v x) f)
  | TensorCollection x y z v => Collection x (fun i => Collection y (fun j => Collection z (fun k => warps (v i j k) f)))
  | grid (x,y,z) (x',y',z') g => Collection x (fun i => Collection y (fun j => Collection z (fun k => (warp_aux (x',y',z') (i,j,k) (g i j k) f))))
  | block (x,y,z) (idx,idy,idz) b => warp_aux (x,y,z) (idx,idy,idz) b f
  | _ => Error
end.

Fixpoint blocks (e : execution_resource) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => blocks (v x))
  | TensorCollection x y z v => Collection z (fun k => Collection y (fun j => Collection x (fun i => blocks (v i j k))))
  | grid (x,y,z) shp' g => TensorCollection x y z (fun i j k => block shp' (i,j,k) (g i j k))
  | _ => Error
end.

Fixpoint threads (e : execution_resource) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => threads (v x))
  | TensorCollection x y z v => Collection z (fun k => Collection y (fun j => Collection x (fun i =>  threads (v i j k))))
  | grid (x,y,z) (x',y',z') g => Collection z (fun k => Collection y (fun j => Collection x (fun i => TensorCollection x' y' z' (fun i' j' k' => lthread (g i j k i' j' k')))))
  | block (x,y,z) _ b => TensorCollection x y z (fun i j k => lthread (b i j k))
  | warp w => TensorCollection Warp_size 1 1 (fun i _ _ => thread (w i))
  | _ => Error
end.

Fixpoint translate (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : execution_resource :=
  (* transform logical threads in physical threads using the translation of address f *)
  match e with
  | Collection n v => Collection n (fun x => translate (v x) f)
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => translate (v i j k) f)
  | lthread i => thread (f i)
  | _ => e
end.

Fixpoint simplify (e : execution_resource) : execution_resource :=
  (* Simplify collections of size 1 *)
  match e with
  | Collection 1 v => simplify (v 0)
  | Collection n v => Collection n (fun i => simplify (v i))
  | TensorCollection 1 1 1 v => simplify (v 0 0 0)
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => simplify (v i j k))
  | _ => e
end.

Notation "e [ l , r ] d" := (sub_selection e l r d) (at level 60).
Notation "e .forall d" := (for_all e d) (at level 60).
Notation "e .threads" := (threads e) (at level 60).
Notation "e .warps" := (warps e) (at level 60).
Notation "e .blocks" := (blocks e) (at level 60).

(* Examples with Warp_size := 8 *)


Example test1 :
  to_list (Block (XZ 2 4)) =
  @ block (XZ 2 4) (0,0,0) (fun i j k : nat => ((0,0,0),(i, j, k))).
Proof.
  simpl.
  reflexivity.
Qed.

Example test2 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (simplify (translate (for_all (for_all (for_all
      (threads (Block (XYZ 2 2 2))) _z) _y) _x) f_addr)) =
    [[[@ thread 0 :: @ thread 1 :: []] :: [@ thread 2 :: @ thread 3 :: []] :: []]
 :: [[@ thread 4 :: @ thread 5 :: []] :: [@ thread 6 :: @ thread 7 :: []] :: []] :: []].
Proof.
  simpl.
  reflexivity.
Qed.

Example test3 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (simplify (translate (for_all (sub_selection (for_all
      (threads (Block (XYZ 2 5 2))) _z) 2 4 _y) _x) f_addr)) =
    [[[@ thread 4 :: @ thread 5 :: []] :: [@ thread 6 :: @ thread 7 :: []] :: []]
 :: [[@ thread 8 :: @ thread 9 :: []] :: [@ thread 10 :: @ thread 11 :: []] :: []] :: []].
Proof.
  simpl.
  reflexivity.
Qed.

Example test4 :
  let f_addr := get_physical_id (2,2,1) (2,2,1) in
  to_list (simplify (translate (
      (threads (Grid (XY 2 2) (XY 1 1)))) f_addr)) =
  [[@ thread 0 :: @ thread 8 :: []] :: [@ thread 16 :: @ thread 24 :: []] :: []]
.
Proof.
  simpl.
  rewrite Warp_size_value_8.
  simpl.
  reflexivity.
Qed.

Example test5 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (simplify (for_all (threads (warps (Block (XYZ 3 2 2)) f_addr)) _x)) =
[   [@ thread 0 :: @ thread 1 :: @ thread 2 :: @ thread 3 :: @ thread 4 :: @ thread 5 :: @ thread 6 :: @ thread 7 :: []]
::  [@ thread 8 :: @ thread 9 :: @ thread 10 :: @ thread 11 :: @ thread 12 :: @ thread 13 :: @ thread 14 :: @ thread 15 :: []]
:: []].
Proof.
  simpl.
  rewrite Warp_size_value_8.
  simpl.
  reflexivity.
Qed.

(* gpu.grid⟨xy⟨2, 2⟩, xy⟨4, 4⟩⟩.blocks.forall(y) *)
Example example :
  to_list (for_all (blocks (Grid (XY 2 2) (XY 4 4))) _y) =
[
  [[[@ block (XY 4 4) (0, 0, 0) (fun i j k : nat => (0, 0, 0, (i, j, k)))
  :: @ block (XY 4 4) (1, 0, 0) (fun i j k : nat => (1, 0, 0, (i, j, k)))
  :: []]
:: []] :: []]
  :: [[[@ block (XY 4 4) (0, 1, 0) (fun i j k : nat => (0, 1, 0, (i, j, k)))
  :: @ block (XY 4 4) (1, 1, 0) (fun i j k : nat => (1, 1, 0, (i, j, k)))
  :: []]
:: []] :: []]
:: []].
Proof.
  simpl.
  reflexivity.
Qed.

(* gpu.grid⟨xy⟨2, 2⟩, xy⟨4, 4⟩⟩.blocks.forall(y).forall(x).threads[0..1]y *)
Example example2 :
  (to_list (simplify (sub_selection (threads (for_all (for_all (blocks (Grid (XY 2 2) (XY 4 4))) _y) _x)) 0 1 _y))) =
[[
      [[[@ lthread ((0, 0, 0), (0, 0, 0))
      :: @ lthread ((0, 0, 0), (1, 0, 0))
      :: @ lthread ((0, 0, 0), (2, 0, 0))
      :: @ lthread ((0, 0, 0), (3, 0, 0)) :: []] :: []] :: []]
  ::  [[[@ lthread ((1, 0, 0), (0, 0, 0))
      :: @ lthread ((1, 0, 0), (1, 0, 0))
      :: @ lthread ((1, 0, 0), (2, 0, 0))
      :: @ lthread ((1, 0, 0), (3, 0, 0)) :: []] :: []] :: []]
  :: []]
:: [
      [[[@ lthread ((0, 1, 0), (0, 0, 0))
      :: @ lthread ((0, 1, 0), (1, 0, 0))
      :: @ lthread ((0, 1, 0), (2, 0, 0))
      :: @ lthread ((0, 1, 0), (3, 0, 0)) :: []] :: []] :: []]
  ::  [[[@ lthread ((1, 1, 0), (0, 0, 0))
      :: @ lthread ((1, 1, 0), (1, 0, 0))
      :: @ lthread ((1, 1, 0), (2, 0, 0))
      :: @ lthread ((1, 1, 0), (3, 0, 0)) :: []] :: []] :: []]
  :: []]
:: []]
.
Proof.
  simpl.
  reflexivity.
Qed.


Example blocks_threads_vs_threads :
  forall shp shp' g,
  threads (blocks (grid shp shp' g)) = threads (grid shp shp' g).
Proof.
  intros. destruct shp as [[x y] z].
  destruct shp' as [[x' y'] z'].
  simpl. reflexivity.
Qed.



















