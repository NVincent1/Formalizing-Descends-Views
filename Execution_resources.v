
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

Inductive Thread_t : Type :=
  | t (id : nat)
.


Definition shape : Type := nat * nat * nat.

Definition Matrix (T : Type) (shp : shape) : Type :=
  match shp with | (x,y,z) => Idx x -> Idx y -> Idx z -> T
end.

Definition Vector (T : Type) (n : nat) : Type :=
  Idx n -> T
.

Definition Warp_t : Type := Vector Thread_t 32.
Definition Block_t (shp : shape) : Type :=
      match shp with | (x,y,z) => Matrix Thread_t (x, y, z) end.
Definition Grid_t (shp : shape) (shp' : shape) : Type :=
      match shp with | (x,y,z) => Matrix (Block_t shp') (x, y, z) end.

Inductive execution_resource : Type :=
  | thread (t : Thread_t)
  | warp (w : Warp_t)
  | block (shp : shape) (b : Block_t shp)
  | grid (shp : shape) (shp' : shape) (g : Grid_t shp shp')
  | Collection (n : nat) (content : Vector execution_resource n)
  | Error
.


Definition build_block (shp : shape) (offset : nat) : Block_t shp :=
  match shp with
  | (x,y,z) => fun i j k => (t (offset + to_nat i + x*(to_nat j) + x*y*(to_nat k)))
end.

Definition build_grid (shp : shape) (shp' : shape) : Grid_t shp shp' :=
  match shp with
  | (x,y,z) => fun i j k => (build_block shp' (to_nat i + x*(to_nat j) + x*y*(to_nat k)))
end.

Definition build_warp : Warp_t :=
  fun i => (t (to_nat i))
.

Definition Thread (id : nat) := thread (t id).
Definition Warp := warp build_warp.
Definition Block (shp : shape) := block shp (build_block shp 0).
Definition Grid (shp : shape) (shp' : shape) := grid shp shp' (build_grid shp shp').

Inductive dimension : Type :=
  | _x | _y | _z
.


Fixpoint for_all (e : execution_resource) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => for_all (v x) d)
  | grid (x,1,1) shp' g, _x => Collection x (fun i => block shp' (g i zero zero))
  | grid (1,y,1) shp' g, _y => Collection y (fun j => block shp' (g zero j zero))
  | grid (1,1,z) shp' g, _z => Collection z (fun k => block shp' (g zero zero k))
  | grid (1,_,_) _ _, _x => Error
  | grid (_,1,_) _ _, _y => Error
  | grid (_,_,1) _ _, _z => Error
  | grid (x,y,z) shp' g, _x => Collection x (fun i => grid (1,y,z) shp' (fun _ j k => g i j k))
  | grid (x,y,z) shp' g, _y => Collection y (fun j => grid (x,1,z) shp' (fun i _ k => g i j k))
  | grid (x,y,z) shp' g, _z => Collection z (fun k => grid (x,y,1) shp' (fun i j _ => g i j k))
  | block (x,1,1) b, _x => Collection x (fun i => thread (b i zero zero))
  | block (1,y,1) b, _y => Collection y (fun j => thread (b zero j zero))
  | block (1,1,z) b, _z => Collection z (fun k => thread (b zero zero k))
  | block (1,_,_) _, _x => Error
  | block (_,1,_) _, _y => Error
  | block (_,_,1) _, _z => Error
  | block (x,y,z) b, _x => Collection x (fun i => block (1,y,z) (fun _ j k => b i j k))
  | block (x,y,z) b, _y => Collection y (fun j => block (x,1,z) (fun i _ k => b i j k))
  | block (x,y,z) b, _z => Collection z (fun k => block (x,y,1) (fun i j _ => b i j k))
  | warp w, _x => Collection 32 (fun i => thread (w i))
  | _,_ => Error
end.

Inductive Nested_List (T : Type) : Type :=
  | Elt (x : T)
  | Nest (l : List (Nested_List T))
.

Fixpoint to_list (e : execution_resource) : Nested_List execution_resource :=
  match e with
  | Collection n v => Nest _ (rev (buildList (fun i => to_list (v i))))
  | _ => Elt _ e
end.

Notation "[ l ]" := (Nest _ l).
Notation "# x" := (Elt _ x) (at level 20).

Definition shiftBounded {a : nat} {b : nat} {n : nat} {i : Idx (b-a)} :
  a + to_nat i < n.
Proof.
Admitted.

Definition shift {n : nat} {b : nat} {a : nat} (i : Idx (b-a)) : Idx n :=
  idx n (a + to_nat i) shiftBounded.

Fixpoint select (e : execution_resource) (l : nat) (r : nat) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => select (v x) l r d)
  | grid (_,1,1) shp' g, _x => Collection (r-l) (fun i => block shp' (g (shift i) zero zero))
  | grid (1,_,1) shp' g, _y => Collection (r-l) (fun j => block shp' (g zero (shift j) zero))
  | grid (1,1,_) shp' g, _z => Collection (r-l) (fun k => block shp' (g zero zero (shift k)))
  | grid (1,_,_) _ _, _x => Error
  | grid (_,1,_) _ _, _y => Error
  | grid (_,_,1) _ _, _z => Error
  | grid (_,y,z) shp' g, _x => Collection (r-l) (fun i => grid (1,y,z) shp' (fun _ j k => g (shift i) j k))
  | grid (x,_,z) shp' g, _y => Collection (r-l) (fun j => grid (x,1,z) shp' (fun i _ k => g i (shift j) k))
  | grid (x,y,_) shp' g, _z => Collection (r-l) (fun k => grid (x,y,1) shp' (fun i j _ => g i j (shift k)))
  | block (_,1,1) b, _x => Collection (r-l) (fun i => thread (b (shift i) zero zero))
  | block (1,_,1) b, _y => Collection (r-l) (fun j => thread (b zero (shift j) zero))
  | block (1,1,_) b, _z => Collection (r-l) (fun k => thread (b zero zero (shift k)))
  | block (1,_,_) _, _x => Error
  | block (_,1,_) _, _y => Error
  | block (_,_,1) _, _z => Error
  | block (_,y,z) b, _x => Collection (r-l) (fun i => block (1,y,z) (fun _ j k => b (shift i) j k))
  | block (x,_,z) b, _y => Collection (r-l) (fun j => block (x,1,z) (fun i _ k => b i (shift j) k))
  | block (x,y,_) b, _z => Collection (r-l) (fun k => block (x,y,1) (fun i j _ => b i j (shift k)))
  | warp w, _x => Collection 32 (fun i => thread (w i))
  | _,_ => Error
end.

Example test :
  to_list (for_all (for_all (select (Block (3,2,100)) 0 2 _z) _y) _x) = [ [] ].
Proof.
  simpl. unfold crop. simpl.
  



