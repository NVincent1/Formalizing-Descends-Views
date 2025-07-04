
From Views Require Import utils.
Require Import PeanoNat.
From Views Require Import BoundedInt.




(* Inductive execlevel: Type :=
  | Blocks
  | Warps
  | Threads.
Inductive filtersize: Type := FilterSize (l: execlevel) (d size: nat).
Inductive execty: Type :=
  | TyGpuGrid {num_dims : nat} (gs bs : @DimSizes num_dims) (filtersizes: list filtersize)
  | TyHostThread.
Inductive execrange: Type := Range (lower upper: nat) (is_distrib: bool).
Inductive filter: Type := Filter (l: execlevel) (d: nat) (r: execrange).
Inductive execexpr: Type :=
  | HostThread
  | GpuGrid {num_dims : nat} (grid_size block_size : @DimSizes num_dims) (filter: list filter)
  | ExecVar (ident: string).
Inductive exec_distrib: Type :=
  | Distrib (ed: exec_distrib) (distribs: list (execlevel * nat)). *)



Definition shape : Type := nat * nat * nat.
Notation "XYZ< x y z >" := (x,y,z).
Notation "XY< x y >" := (x,y,1).
Notation "XZ< x z >" := (x,1,z).
Notation "YZ< y z >" := (1,y,z).
Notation "X< x >" := (x,1,1).
Notation "Y< y >" := (1,y,1).
Notation "Z< z >" := (1,1,z).

Definition XYZ (x y z : nat) := (x,y,z).
Definition XY (x y : nat) := (x,y,1).
Definition XZ (x z : nat) := (x,1,z).
Definition YZ (y z : nat) := (1,y,z).
Definition X (x : nat) := (x,1,1).
Definition Y (y : nat) := (1,y,1).
Definition Z (z : nat) := (1,1,z).

Definition Matrix (T : Type) (shp : shape) : Type :=
  match shp with | (x,y,z) => nat -> nat -> nat -> T
end.

Definition Vector (T : Type) (n : nat) : Type :=
  nat -> T
.

Definition Thread_t : Type := nat.
Definition Warp_t (n : nat) : Type := Vector Thread_t n.
Definition Block_t (shp : shape) : Type :=
      match shp with | (x,y,z) => Matrix Thread_t (x, y, z) end.
Definition Grid_t (shp : shape) (shp' : shape) : Type :=
      match shp with | (x,y,z) => Matrix (Block_t shp') (x, y, z) end.

Inductive execution_resource : Type :=
  | thread (t : Thread_t)
  | warp (n : nat) (w : Warp_t n)
  | block (shp : shape) (b : Block_t shp)
  | grid (shp : shape) (shp' : shape) (g : Grid_t shp shp')
  | Collection (n : nat) (content : Vector execution_resource n)
  | Error
.


Definition build_block (shp : shape) (offset : nat) : Block_t shp :=
  match shp with
  | (x,y,z) => fun i j k => (offset + i + x*j + x*y*k)
end.

Definition build_grid (shp : shape) (shp' : shape) : Grid_t shp shp' :=
  match shp with
  | (x,y,z) => fun i j k => (build_block shp' (i + x* j + x*y*k))
end.

Definition build_warp (n : nat) : Warp_t n :=
  fun i => i
.

Definition Thread (id : nat) := thread id.
Definition Warp (sz : nat) := warp sz (build_warp sz).
Definition Block (shp : shape) := block shp (build_block shp 0).
Definition Grid (shp : shape) (shp' : shape) := grid shp shp' (build_grid shp shp').

Inductive dimension :=
  | _x | _y | _z
.

Fixpoint for_all (e : execution_resource) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => for_all (v x) d)
  | grid (x,1,1) shp' g, _x => Collection x (fun i => block shp' (g i 0 0))
  | grid (1,y,1) shp' g, _y => Collection y (fun j => block shp' (g 0 j 0))
  | grid (1,1,z) shp' g, _z => Collection z (fun k => block shp' (g 0 0 k))
  | grid (1,_,_) _ _, _x => Error
  | grid (_,1,_) _ _, _y => Error
  | grid (_,_,1) _ _, _z => Error
  | grid (x,y,z) shp' g, _x => Collection x (fun i => grid (1,y,z) shp' (fun _ j k => g i j k))
  | grid (x,y,z) shp' g, _y => Collection y (fun j => grid (x,1,z) shp' (fun i _ k => g i j k))
  | grid (x,y,z) shp' g, _z => Collection z (fun k => grid (x,y,1) shp' (fun i j _ => g i j k))
  | block (x,1,1) b, _x => Collection x (fun i => thread (b i 0 0))
  | block (1,y,1) b, _y => Collection y (fun j => thread (b 0 j 0))
  | block (1,1,z) b, _z => Collection z (fun k => thread (b 0 0 k))
  | block (1,_,_) _, _x => Error
  | block (_,1,_) _, _y => Error
  | block (_,_,1) _, _z => Error
  | block (x,y,z) b, _x => Collection x (fun i => block (1,y,z) (fun _ j k => b i j k))
  | block (x,y,z) b, _y => Collection y (fun j => block (x,1,z) (fun i _ k => b i j k))
  | block (x,y,z) b, _z => Collection z (fun k => block (x,y,1) (fun i j _ => b i j k))
  | warp sz w, _x => Collection sz (fun i => thread (w i))
  | _,_ => Error
end.

Inductive Nested_List (T : Type) : Type :=
  | Elt (x : T)
  | Nest (l : List (Nested_List T))
.

Fixpoint to_list (e : execution_resource) : Nested_List execution_resource :=
  match e with
  | Collection n v => Nest _ (rev (buildList n (fun i => to_list (v i))))
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

Fixpoint select (e : execution_resource) (l : nat) (r : nat) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => select (v x) l r d)
  | grid (x,1,1) shp' g, _x => assert (r <=? x) (Collection (r-l) (fun i => block shp' (g (i+l) 0 0)))
  | grid (1,y,1) shp' g, _y => assert (r <=? y) (Collection (r-l) (fun j => block shp' (g 0 (j+l) 0)))
  | grid (1,1,z) shp' g, _z => assert (r <=? z) (Collection (r-l) (fun k => block shp' (g 0 0 (k+l))))
  | grid (1,_,_) _ _, _x => Error
  | grid (_,1,_) _ _, _y => Error
  | grid (_,_,1) _ _, _z => Error
  | grid (x,y,z) shp' g, _x => assert (r <=? x) (Collection (r-l) (fun i => grid (1,y,z) shp' (fun _ j k => g (i+l) j k)))
  | grid (x,y,z) shp' g, _y => assert (r <=? y) (Collection (r-l) (fun j => grid (x,1,z) shp' (fun i _ k => g i (j+l) k)))
  | grid (x,y,z) shp' g, _z => assert (r <=? z) (Collection (r-l) (fun k => grid (x,y,1) shp' (fun i j _ => g i j (k+l))))
  | block (x,1,1) b, _x => assert (r <=? x) (Collection (r-l) (fun i => thread (b (i+l) 0 0)))
  | block (1,y,1) b, _y => assert (r <=? y) (Collection (r-l) (fun j => thread (b 0 (j+l) 0)))
  | block (1,1,z) b, _z => assert (r <=? z) (Collection (r-l) (fun k => thread (b 0 0 (k+l))))
  | block (1,_,_) _, _x => Error
  | block (_,1,_) _, _y => Error
  | block (_,_,1) _, _z => Error
  | block (x,y,z) b, _x => assert (r <=? x) (Collection (r-l) (fun i => block (1,y,z) (fun _ j k => b (i+l) j k)))
  | block (x,y,z) b, _y => assert (r <=? y) (Collection (r-l) (fun j => block (x,1,z) (fun i _ k => b i (j+l) k)))
  | block (x,y,z) b, _z => assert (r <=? z) (Collection (r-l) (fun k => block (x,y,1) (fun i j _ => b i j (k+l))))
  | warp sz w, _x => Collection sz (fun i => thread (w i))
  | _,_ => Error
end.

Example test1 :
  to_list (Block (XZ 2 4)) =
  @ block (XZ 2 4) (fun i j k : nat => i + 2*j + 2*k).
Proof.
  simpl.
  reflexivity.
Qed.

Example test2 :
  to_list (select (Block (XZ 2 4)) 1 3 _z) =
  [@ block (X 2) (fun i j _ : nat => i + 2*j + 2) :: @ block (X 2) (fun i j _ : nat => i + 2*j + 4) :: []].
Proof.
  simpl.
  reflexivity.
Qed.

Example test3 :
  to_list (for_all (select (Block (XZ 2 4)) 1 3 _z) _x) =
  [[@ thread 2 :: @ thread 3 :: []] :: [@ thread 4 :: @ thread 5 :: []] :: []].
Proof.
  simpl.
  reflexivity.
Qed.






















