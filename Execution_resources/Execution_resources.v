
From Views Require Import utils.
Require Import PeanoNat.

Definition Warp_size : nat.
Proof. apply 0. Qed.
Axiom Warp_size_value :
  Warp_size = 8.

Definition shape : Type := nat * nat * nat.
(* Notation "XYZ< x y z >" := (x,y,z).
Notation "XY< x y >" := (x,y,1).
Notation "XZ< x z >" := (x,1,z).
Notation "YZ< y z >" := (1,y,z).
Notation "X< x >" := (x,1,1).
Notation "Y< y >" := (1,y,1).
Notation "Z< z >" := (1,1,z). *)

Definition size (shp : shape) :=
  match shp with | (x,y,z) => x*y*z
end.

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

Definition Tensor' (T : Type) (x y z : nat) : Type :=
  nat -> nat -> nat -> T
.

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
  | TensorCollection (x y z : nat) (content : Tensor' execution_resource x y z)
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

Definition address_mapping := LogicalId_t * LogicalId_t -> PhysicalId_t.

Fixpoint build_collection (n : nat) (l : nat) (v : Vector execution_resource l) : execution_resource :=
  match n with
  | 0 => Collection l v
  | S n => match (v n) with
           | Error => Error
           | _ => build_collection n l v
           end
end.

Fixpoint for_all (e : execution_resource) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun i => for_all (v i) d)
  | TensorCollection x y z v, _x => Collection x (fun i => TensorCollection 1 y z (fun _ j k => v i j k))
  | TensorCollection x y z v, _y => Collection y (fun j => TensorCollection x 1 z (fun i _ k => v i j k))
  | TensorCollection x y z v, _z => Collection z (fun k => TensorCollection x y 1 (fun i j _ => v i j k))
  | _,_ => Error
end.

Inductive Nested_List (T : Type) : Type :=
  | Elt (x : T)
  | Nest (l : List (Nested_List T))
.

Fixpoint to_list (e : execution_resource) : Nested_List execution_resource :=
  match e with
  | Collection n v => Nest _ (rev (buildList n (fun i => to_list (v i))))
  | TensorCollection x y z v => Nest _ (rev (buildList z (fun k => 
                                Nest _ (rev (buildList y (fun j =>
                                Nest _ (rev (buildList x (fun i => to_list (v i j k))))))))))
  | _ => Elt _ e
end.

Notation "[ l ]" := (Nest _ l).
Notation "@ x" := (Elt _ x) (at level 20).

Fixpoint leb (x : nat) (y : nat) : bool :=
  match x,y with
  | 0,_ => true
  | _,0 => false
  | S x, S y => (leb x y)
end.

Notation "x <=? y" := (leb x y).

Definition assert (cond : bool) (success : execution_resource) : execution_resource :=
  if cond then success else Error.

Fixpoint select_range (e : execution_resource) (l : nat) (r : nat) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => select_range (v x) l r d)
  | TensorCollection x y z v, _x => assert (r <=? x) (Collection (r-l) (fun i => TensorCollection 1 y z (fun _ j k => v (i+l) j k)))
  | TensorCollection x y z v, _y => assert (r <=? y) (Collection (r-l) (fun j => TensorCollection x 1 z (fun i _ k => v i (j+l) k)))
  | TensorCollection x y z v, _z => assert (r <=? z) (Collection (r-l) (fun k => TensorCollection x y 1 (fun i j _ => v i j (k+l))))
  | _,_ => Error
end.

Fixpoint blocks (e : execution_resource) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => blocks (v x))
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => blocks (v i j k))
  | grid (x,y,z) shp' g => TensorCollection x y z (fun i j k => block shp' (i,j,k) (g i j k))
  | _ => Error
end.

Fixpoint threads (e : execution_resource) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => threads (v x))
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => threads (v i j k))
  | grid (x,y,z) (x',y',z') g => TensorCollection x y z (fun i j k => TensorCollection x' y' z' (fun i' j' k' => lthread (g i j k i' j' k')))
  | block (x,y,z) _ b => TensorCollection x y z (fun i j k => lthread (b i j k))
  | warp w => TensorCollection Warp_size 1 1 (fun i _ _ => thread (w i))
  | _ => Error
end.

Definition get_logical_id (shp : shape) : ThreadId_t -> LogicalId_t :=
  fun i =>
  match shp,i with
  | (x',y',z'),((i,j,k),(i',j',k')) =>
  (i*x'+i',j*y'+j',k*z'+k')
end.


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

Definition get_physical_id (shp : shape) (shp' : shape) : ThreadId_t -> PhysicalId_t :=
  fun id =>
  match shp,shp',id with
  | (x,y,z),(x',y',z'),((i,j,k),(i',j',k')) =>
    let w := next_multiple x' Warp_size in
    i*w+i' + x*w*(j*y'+j') + x*y*w*y'*(k*z'+k')
end.

Definition warp_aux (shp : shape) (id : shape) (b : Block_t shp) (f : ThreadId_t -> PhysicalId_t) :=
  match shp,id with
  | (x,y,z),(idx,idy,idz) => TensorCollection ((next_multiple x Warp_size)/Warp_size) y z
                               (fun i j k =>  warp (fun i' => f ((idx,idy,idz),(i*Warp_size+i',j,k))))
end.

Fixpoint warps (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => warps (v x) f)
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => warps (v i j k) f)
  | grid (x,y,z) (x',y',z') g => Collection x (fun i => Collection y (fun j => Collection z (fun k => (warp_aux (x',y',z') (i,j,k) (g i j k) f))))
  | block (x,y,z) (idx,idy,idz) b => warp_aux (x,y,z) (idx,idy,idz) b f
  | warp w => e
  | _ => Error
end.

Fixpoint translate (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => translate (v x) f)
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => translate (v i j k) f)
  | lthread i => thread (f i)
  | _ => e
end.

Fixpoint simplify (e : execution_resource) : execution_resource :=
  match e with
  | Collection 1 v => simplify (v 0)
  | Collection n v => Collection n (fun i => simplify (v i))
  | TensorCollection 1 1 1 v => simplify (v 0 0 0)
  | TensorCollection x y z v => TensorCollection x y z (fun i j k => simplify (v i j k))
  | _ => e
end.

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
    [[[@ thread 0 :: @ thread 1 :: []] :: [@ thread 8 :: @ thread 9 :: []] :: []]
 :: [[@ thread 16 :: @ thread 17 :: []] :: [@ thread 24 :: @ thread 25 :: []] :: []] :: []].
Proof.
  simpl.
  rewrite Warp_size_value.
  simpl.
  reflexivity.
Qed.

Example test3 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (simplify (translate (for_all (select_range (for_all
      (threads (Block (XYZ 2 5 2))) _z) 2 4 _y) _x) f_addr)) =
    [[[@ thread 16 :: @ thread 17 :: []] :: [@ thread 24 :: @ thread 25 :: []] :: []]
 :: [[@ thread 32 :: @ thread 33 :: []] :: [@ thread 40 :: @ thread 41 :: []] :: []] :: []].
Proof.
  simpl.
  rewrite Warp_size_value.
  simpl.
  reflexivity.
Qed.

Example test4 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (simplify (for_all (threads (warps (Block (XYZ 2 2 2)) f_addr)) _x)) =
[
[[
  [[[@ thread 0 :: @ thread 1 :: @ thread 2 :: @ thread 3
  :: @ thread 4 :: @ thread 5 :: @ thread 6 :: @ thread 7
  :: []] :: []] :: []] :: []]
  :: [
  [[[@ thread 8 :: @ thread 9 :: @ thread 10 :: @ thread 11
  :: @ thread 12 :: @ thread 13 :: @ thread 14 :: @ thread 15
  :: []] :: []] :: []] :: []]
:: []]
:: [[
  [[[@ thread 16 :: @ thread 17 :: @ thread 18 :: @ thread 19
  :: @ thread 20 :: @ thread 21 :: @ thread 22 :: @ thread 23
  :: []] :: []] :: []] :: []]
  :: [
  [[[@ thread 24 :: @ thread 25 :: @ thread 26 :: @ thread 27
  :: @ thread 28 :: @ thread 29 :: @ thread 30 :: @ thread 31
  :: []] :: []] :: []] :: []]
:: []]
:: []].
Proof.
  simpl.
  rewrite Warp_size_value.
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



















