
From Views Require Import utils.
Require Import PeanoNat.

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


Inductive dimension : Type :=
  | _x | _y | _z
.

Inductive shape : Type :=
  | XYZ (x : nat) (y : nat) (z : nat)
  | XY (x : nat) (y : nat)
  | XZ (x : nat) (z : nat)
  | YZ (y : nat) (z : nat)
  | X (x : nat)
  | Y (y : nat)
  | Z (z : nat)
.

Inductive execution_resource : Type :=
  | Grid (s : shape) (s' : shape) (offset : nat) (step : nat*nat)
  | Block (s : shape) (offset : nat) (step : nat*nat)
  | Warp (offset : nat)
  | Thread (id : nat)
.

Definition shapesize (s : shape) :=
  match s with
  | XYZ x y z => x*y*z
  | XY x y => x*y
  | XZ x z => x*z
  | YZ y z => y*z
  | X x => x
  | Y y => y
  | Z z => z
end.

Definition size (e : execution_resource) : nat :=
  match e with
  | Grid s s' _ _ => shapesize s * shapesize s'
  | Block s _ _ => shapesize s
  | Warp _ => 32
  | Thread _ => 1
end.

Definition access_dimension (s : shape) (d : dimension) : option shape * nat :=
  match s,d with
  | XYZ x y z, _x => (Some (YZ y z), x)
  | XYZ x y z, _y => (Some (XZ x z), y)
  | XYZ x y z, _z => (Some (XY x y), z)
  | XY x y, _x => (Some (Y y), x)
  | XY x y, _y => (Some (X x), y)
  | XZ x z, _x => (Some (Z z), x)
  | XZ x z, _z => (Some (X x), z)
  | YZ y z, _y => (Some (Z z), y)
  | YZ y z, _z => (Some (Y y), z)
  | X x, _x => (None, x)
  | Y y, _y => (None, y)
  | Z z, _z => (None, z)
  | _,_ => (None,0)
end.

Fixpoint decompose (l : nat) (e : execution_resource) (offset : nat) (size : nat) : List execution_resource :=
  match l with
  | 0 => []
  | S l => match e with
           | Grid s s' b step => Grid s s' (b+offset) step
           | Block s b step => Block s (b+offset) step
           | Warp b => Warp (b+offset)
           | Thread id => Thread (id+offset)
           end :: (decompose l e (offset+size) size)
end.

Definition get_x (s : shape) :=
  match s with
  | XYZ x _ _ | XY x _ | XZ x _ | X x => x
  | _ => 1
end.

Definition get_y (s : shape) :=
  match s with
  | XYZ _ y _ | XY _ y | YZ y _ | Y y => y
  | _ => 1
end.

Definition get_z (s : shape) :=
  match s with
  | XYZ _ _ z | XZ _ z | YZ _ z | Z z => z
  | _ => 1
end.


Definition get_offset (e : execution_resource) (d : dimension) : nat :=
  match e with
  | Grid s s' b _ => match d with
                   | _x => size (Block s' b (0,0))
                   | _y => (get_x s) * size (Block s' b (0,0))
                   | _z => (get_x s) * (get_y s) * size (Block s' b (0,0))
                   end
  | Block s b _ => match d with
                 | _x => (get_x s) * size (Thread b)
                 | _y => (get_y s) * size (Thread b)
                 | _z => (get_z s) * size (Thread b)
                 end
  | Warp _ => 32
  | Thread _ => 1
end.

Definition for_all (d : dimension) (e : execution_resource) : List (execution_resource) :=
  match e with
  | Grid s0 s' offset (sx,sz) => match (access_dimension s0 d),d with
                        | (Some s, l),_x => decompose l (Grid s s' offset (sx,sz)) 0 (sx*(get_y s0))
                        | (Some s, l),_y => decompose l (Grid s s' offset (sx*get_y s0,sz)) 0 sx
                        | (Some s, l),_z => decompose l (Grid s s' offset (sx,sz/(get_x s0))) 0 sz
                        | (None, l),_x => decompose l (Block s' (offset*shapesize s') (1,get_x s' * get_z s')) 0 (sx*shapesize s')
                        | (None, l),_y => decompose l (Block s' (offset*shapesize s') (1,get_x s' * get_z s')) 0 (sx*shapesize s')
                        | (None, l),_z => decompose l (Block s' (offset*shapesize s') (1,get_x s' * get_z s')) 0 (sz*shapesize s')
                        end
  | Block s0 offset (sx,sz) => match (access_dimension s0 d),d with
                        | (Some s, l),_x => decompose l (Block s offset (sx,sz)) 0 (sx*(get_y s0))
                        | (Some s, l),_y => decompose l (Block s offset (sx*get_y s0,sz)) 0 sx
                        | (Some s, l),_z => decompose l (Block s offset (sx,sz/(get_x s0))) 0 sz
                        | (None, l),_x => decompose l (Thread offset) 0 sx
                        | (None, l),_y => decompose l (Thread offset) 0 sx
                        | (None, l),_z => decompose l (Thread offset) 0 sz
                        end
  | Warp offset => decompose 32 (Thread offset) 0 1
  | _ => []
end.


Definition grid (s : shape) (s' : shape) := Grid s s' 0 (1,get_x s * get_z s).
Definition block (s : shape) := Block s 0 (1,get_x s * get_z s).
Definition warp := Warp 0.
Definition thread (id : nat) := Thread id.







