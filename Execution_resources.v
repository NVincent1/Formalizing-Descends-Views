
From Views Require Import utils.

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

Fixpoint shapelist (size : nat) (x : shape) : List shape :=
  match size with
  | 0 => []
  | S n => x :: (shapelist n x)
end.

Definition for_all (d : dimension) (s : shape) : List shape :=
  match (s,d) with
  | (XYZ x y z, _x) => shapelist x (YZ y z)
  | (XYZ x y z, _y) => shapelist y (XZ x z)
  | (XYZ x y z, _z) => shapelist z (XY x y)
  | (XY x y, _x) => shapelist x (Y y)
  | (XY x y, _y) => shapelist y (X x)
  | (XZ x z, _x) => shapelist x (Z z)
  | (XZ x z, _z) => shapelist z (X x)
  | (YZ y z, _y) => shapelist y (Z z)
  | (YZ y z, _z) => shapelist z (Y y)
  | _ => []
end.

Example test :
  zip (map (for_all _x) (for_all _y (XYZ 3 4 2))) =
  Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: Z 2 :: [].
simpl. reflexivity.
Qed.


