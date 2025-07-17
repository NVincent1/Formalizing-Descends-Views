
From Views Require Import utils.
Require Import PeanoNat.


Definition Warp_size : nat.
apply 0.
Qed.

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
  | grid (1,_,_) _ _, _x => Error
  | grid (_,1,_) _ _, _y => Error
  | grid (_,_,1) _ _, _z => Error
  | grid (x,1,1) shp' g, _x => Collection x (fun i => block shp' (i,0,0) (g i 0 0))
  | grid (1,y,1) shp' g, _y => Collection y (fun j => block shp' (0,j,0) (g 0 j 0))
  | grid (1,1,z) shp' g, _z => Collection z (fun k => block shp' (0,0,k) (g 0 0 k))
  | grid (x,y,z) shp' g, _x => Collection x (fun i => grid (1,y,z) shp' (fun _ j k => g i j k))
  | grid (x,y,z) shp' g, _y => Collection y (fun j => grid (x,1,z) shp' (fun i _ k => g i j k))
  | grid (x,y,z) shp' g, _z => Collection z (fun k => grid (x,y,1) shp' (fun i j _ => g i j k))
  | block (1,_,_) _ _, _x => Error
  | block (_,1,_) _ _, _y => Error
  | block (_,_,1) _ _, _z => Error
  | block (x,1,1) _ b, _x => Collection x (fun i => lthread (b i 0 0))
  | block (1,y,1) _ b, _y => Collection y (fun j => lthread (b 0 j 0))
  | block (1,1,z) _ b, _z => Collection z (fun k => lthread (b 0 0 k))
  | block (x,y,z) (id_x,id_y,id_z) b, _x => Collection x (fun i => block (1,y,z) (id_x+i,id_y,id_z) (fun _ j k => b i j k))
  | block (x,y,z) (id_x,id_y,id_z) b, _y => Collection y (fun j => block (x,1,z) (id_x,id_y+j,id_z) (fun i _ k => b i j k))
  | block (x,y,z) (id_x,id_y,id_z) b, _z => Collection z (fun k => block (x,y,1) (id_x,id_y,id_z+k) (fun i j _ => b i j k))
  | warp w, _x => Collection Warp_size (fun i => thread (w i))
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

Fixpoint select_range (e : execution_resource) (l : nat) (r : nat) (d : dimension) : execution_resource :=
  match e,d with
  | Collection n v,_ => Collection n (fun x => select_range (v x) l r d)
  | grid (1,_,_) _ _, _x => Error
  | grid (_,1,_) _ _, _y => Error
  | grid (_,_,1) _ _, _z => Error
  | grid (x,1,1) shp' g, _x => assert (r <=? x) (Collection (r-l) (fun i => block shp' (i,0,0) (g (i+l) 0 0)))
  | grid (1,y,1) shp' g, _y => assert (r <=? y) (Collection (r-l) (fun j => block shp' (0,j,0) (g 0 (j+l) 0)))
  | grid (1,1,z) shp' g, _z => assert (r <=? z) (Collection (r-l) (fun k => block shp' (0,0,k) (g 0 0 (k+l))))
  | grid (x,y,z) shp' g, _x => assert (r <=? x) (Collection (r-l) (fun i => grid (1,y,z) shp' (fun _ j k => g (i+l) j k)))
  | grid (x,y,z) shp' g, _y => assert (r <=? y) (Collection (r-l) (fun j => grid (x,1,z) shp' (fun i _ k => g i (j+l) k)))
  | grid (x,y,z) shp' g, _z => assert (r <=? z) (Collection (r-l) (fun k => grid (x,y,1) shp' (fun i j _ => g i j (k+l))))
  | block (1,_,_) _ _, _x => Error
  | block (_,1,_) _ _, _y => Error
  | block (_,_,1) _ _, _z => Error
  | block (x,1,1) _ b, _x => assert (r <=? x) (Collection (r-l) (fun i => lthread (b (i+l) 0 0)))
  | block (1,y,1) _ b, _y => assert (r <=? y) (Collection (r-l) (fun j => lthread (b 0 (j+l) 0)))
  | block (1,1,z) _ b, _z => assert (r <=? z) (Collection (r-l) (fun k => lthread (b 0 0 (k+l))))
  | block (x,y,z) (id_x,id_y,id_z) b, _x => assert (r <=? x) (Collection (r-l) (fun i => block (1,y,z) (id_x+i,id_y,id_z) (fun _ j k => b (i+l) j k)))
  | block (x,y,z) (id_x,id_y,id_z) b, _y => assert (r <=? y) (Collection (r-l) (fun j => block (x,1,z) (id_x,id_y+j,id_z) (fun i _ k => b i (j+l) k)))
  | block (x,y,z) (id_x,id_y,id_z) b, _z => assert (r <=? z) (Collection (r-l) (fun k => block (x,y,1) (id_x,id_y,id_z+k) (fun i j _ => b i j (k+l))))
  | warp w, _x => assert (r <=? Warp_size) (Collection (r - l) (fun i => thread (w i)))
  | _,_ => Error
end.

Example test1 :
  to_list (Block (XZ 2 4)) =
  @ block (XZ 2 4) (0,0,0) (fun i j k : nat => ((0,0,0),(i, j, k))).
Proof.
  simpl.
  reflexivity.
Qed.

Definition get_logical_id (shp : shape) : ThreadId_t -> LogicalId_t :=
  fun i =>
  match shp,i with
  | (x',y',z'),((i,j,k),(i',j',k')) =>
  (i*x'+i',j*y'+j',k*z'+k')
end.

Fixpoint get_physical_id_aux (shp : shape) (x' y' z' : nat) : ThreadId_t -> PhysicalId_t :=
  fun id =>
  match shp,x',y',z',id with
  | (x,y,z),S x',y',z',((i,j,k),(i',j',k')) =>
    match (S x') mod Warp_size with
    | 0 => i*(S x')+i' + x*(S x')*(j*y'+j') + x*y*(S x')*y'*(k*z'+k')
    | S n => get_physical_id_aux (x,y,z) x' y' z' id
    end
  | (x,y,z),x',y',z',((i,j,k),(i',j',k')) =>
    i*x'+i' + x*x'*(j*y'+j') + x*y*x'*y'*(k*z'+k')
end.

Fixpoint lesser_multiple_aux (n : nat) (m : nat) :=
  match n with
  | 0 => 0
  | S n => match (S n mod m) with
           | 0 => S n
           | _ => lesser_multiple_aux n m
end
end.

Definition lesser_multiple (n : nat) (m : nat) :=
  match (n mod m) with
  | 0 => n
  | _ => lesser_multiple_aux (n + m) m
end.

Definition get_physical_id (shp : shape) (shp' : shape) : ThreadId_t -> PhysicalId_t :=
  fun id =>
  match shp,shp',id with
  | (x,y,z),(x',y',z'),((i,j,k),(i',j',k')) =>
    let w := lesser_multiple x' Warp_size in
    i*w+i' + x*w*(j*y'+j') + x*y*w*y'*(k*z'+k')
end.

Definition warp_aux (shp : shape) (id : shape) (b : Block_t shp) (f : ThreadId_t -> PhysicalId_t) :=
  match shp,id with
  | (x,y,z),(idx,idy,idz) => Collection ((lesser_multiple x Warp_size)/Warp_size) (fun i => Collection y (fun j => Collection z (fun k =>  warp (fun i' => f ((idx,idy,idz),(i*Warp_size+i',j,k))))))
end.

Fixpoint warps (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => warps (v x) f)
  | grid (x,y,z) (x',y',z') g => Collection x (fun i => Collection y (fun j => Collection z (fun k => (warp_aux (x',y',z') (i,j,k) (g i j k) f))))
  | block (x,y,z) (idx,idy,idz) b => warp_aux (x,y,z) (idx,idy,idz) b f
  | warp w => e
  | _ => Error
end.

Fixpoint maptranslate (f : ThreadId_t -> PhysicalId_t) (l : List execution_resource) : List execution_resource :=
  match l with
  | [] => []
  | h :: tl => match h with
               | lthread i => thread (f i)::(maptranslate f tl)
               | _ => h::(maptranslate f tl)
end end.

Fixpoint translate (e : execution_resource) (f : ThreadId_t -> PhysicalId_t) : execution_resource :=
  match e with
  | Collection n v => Collection n (fun x => translate (v x) f)
  | lthread i => thread (f i)
  | _ => e
end.


(* Example test2 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (translate (for_all (for_all (for_all
      (Block (XYZ 2 2 2)) _z) _y) _x) f_addr) =
    [[[@ thread 0 :: @ thread 1 :: []] :: [@ thread 8 :: @ thread 9 :: []] :: []]
 :: [[@ thread 16 :: @ thread 17 :: []] :: [@ thread 24 :: @ thread 25 :: []] :: []] :: []].
Proof.
  simpl.
  reflexivity.
Qed. *)

(* Example test3 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (translate (for_all (select_range (for_all
      (Block (XYZ 2 5 2)) _z) 2 4 _y) _x) f_addr) =
    [[[@ thread 16 :: @ thread 17 :: []] :: [@ thread 24 :: @ thread 25 :: []] :: []]
 :: [[@ thread 32 :: @ thread 33 :: []] :: [@ thread 40 :: @ thread 41 :: []] :: []] :: []].
Proof.
  simpl.
  reflexivity.
Qed. *)


(* Example test4 :
  let f_addr := get_physical_id (1,1,1) (2,2,2) in
  to_list (for_all (warps (Block (XYZ 2 2 2)) f_addr) _x) =
  [[[
[@ thread 0 :: @ thread 1 :: @ thread 2 :: @ thread 3 :: @ thread 4 :: @ thread 5 :: @ thread 6 :: @ thread 7
:: []] :: []]
::
[[@ thread 8 :: @ thread 9 :: @ thread 10 :: @ thread 11 :: @ thread 12 :: @ thread 13 :: @ thread 14 :: @ thread 15
:: []] :: []]
:: []]
::
[[[@ thread 16 :: @ thread 17 :: @ thread 18 :: @ thread 19 :: @ thread 20 :: @ thread 21 :: @ thread 22 :: @ thread 23
:: []] :: []]
::
[[@ thread 24 :: @ thread 25 :: @ thread 26 :: @ thread 27 :: @ thread 28 :: @ thread 29 :: @ thread 30 :: @ thread 31
:: []] :: []]
:: []] :: []].
Proof.
  simpl.
  reflexivity.
Qed. *)






















