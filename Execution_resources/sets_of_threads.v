
From Views Require Import utils.
From Views.Execution_resources Require Import Execution_resources.
Require Import PeanoNat.

Fixpoint thread_set_1z {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => f (m x y z) ++ (thread_set_1z (S x) (S y) z f m)
  | _ => fun _ => []
end.


Fixpoint thread_set_1y {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => f (m x y z) ++ (thread_set_1y (S x) y (S z) f m)
  | _ => fun _ => []
end.

Fixpoint thread_set_2yz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => thread_set_1z (S x) (S y) (S z) f m  ++ (thread_set_2yz (S x) y (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_2xz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => thread_set_1z (S x) (S y) (S z) f m  ++ (thread_set_2xz x (S y) (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_2xy {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
      fun m => thread_set_1y (S x) (S y) (S z) f m  ++ (thread_set_2xy x (S y) (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_3xyz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
         fun m => thread_set_2yz (S x) (S y) (S z) f m ++ (thread_set_3xyz x (S y) (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_3yxz {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
         fun m => thread_set_2xz (S x) (S y) (S z) f m ++ (thread_set_3yxz (S x) y (S z) f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set_3zxy {T : Type} (x y z : nat) (f : T -> List ThreadId_t) : Tensor T (x,y,z) -> List ThreadId_t :=
  match (x,y,z) with
  | (S x, S y, S z) =>
         fun m => thread_set_2xy (S x) (S y) (S z) f m ++ (thread_set_3zxy (S x) (S y) z f m) 
  | _ => fun _ => []
end.

Fixpoint thread_set' (e : execution_resource) : List ThreadId_t :=
  match e with
  | Collection n v => zip (buildList n (fun i => thread_set' (v i)))
  | TensorCollection x y z v => zip (buildList x (fun i => zip (buildList y (fun j => zip (buildList z (fun k => thread_set' (v i j k)))))))
  | grid (x,y,z) (x',y',z') g => thread_set_3xyz x y z (fun b => thread_set_3xyz x' y' z' (fun x => x :: []) b) g
  | block (x,y,z) _ b => thread_set_3xyz x y z (fun x => x :: []) b
  | lthread i => i::[]
  | _ => []
end.

Fixpoint physical_thread_set (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : List PhysicalId_t :=
  match e with
  | Collection n v => zip (buildList n (fun i => physical_thread_set (v i) f))
  | TensorCollection x y z v => zip (buildList x (fun i => zip (buildList y (fun j => zip (buildList z (fun k => physical_thread_set (v i j k) f))))))
  | thread i => i::[]
  | warp w => buildList Warp_size (fun i => w i)
  | _ => map f (thread_set' e)
end.


Inductive count {T : Type} : T -> List T -> nat -> Prop :=
  | empty (x : T) : count x [] 0
  | cons_eq (x : T) (tl : List T) {n : nat} (H : count x tl n) : count x (x::tl) (S n)
  | cons_neq (x : T) (y : T) (tl : List T) {n : nat} (H : count x tl n) (Hneq : x <> y) : count x (y::tl) n
.

Fixpoint no_error (e : execution_resource) (f : execution_resource -> execution_resource) : Prop :=
  match e with
  | Collection n v => forall i, i < n -> (no_error (v i) f)
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> (no_error (v i j k) f)
  | _ => f e <> Error
end.


