(* 
Inductive execlevel: Type :=
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
  | Distrib (ed: exec_distrib) (distribs: list (execlevel * nat)).
 *)