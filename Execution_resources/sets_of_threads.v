
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

Fixpoint logical_thread_set (e : execution_resource) : List ThreadId_t :=
  match e with
  | Collection n v => zip (buildList n (fun i => logical_thread_set (v i)))
  | TensorCollection x y z v => zip (buildList x (fun i => zip (buildList y (fun j => zip (buildList z (fun k => logical_thread_set (v i j k)))))))
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
  | _ => map f (logical_thread_set e)
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

Fixpoint not_physical (e : execution_resource) : Prop :=
  match e with
  | Collection n v => forall i, i < n -> (not_physical (v i))
  | TensorCollection x y z v => forall i j k, i < x -> j < y -> k < z -> (not_physical (v i j k))
  | _ => (forall w, e <> warp w) /\ (forall i, e <> thread i)
end.

Lemma empty_list : 
  forall x T fj,
  (forall (j : nat), fj j = []) ->
  zip (buildList x (fun (j:nat) => (fj j : List T))) = [].
Proof.
  intros. induction x. reflexivity. simpl. rewrite H. apply IHx.
Qed.

(** Rewriting thread_set with buildList *)
Lemma block_ok_z :
forall b x y z,
thread_set_1z (S x) (S y) z (fun x0 : ThreadId_t => x0 :: []) b =
buildList z (fun k => b x y k).
Proof.
  induction z.
    + intros. reflexivity.
    + intros. simpl. rewrite IHz. reflexivity.
Qed.


Lemma block_ok_y :
forall b x y z,
thread_set_1y (S x) y (S z) (fun x0 : ThreadId_t => x0 :: []) b =
buildList y (fun k => b x k z).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl. rewrite IHy. reflexivity.
Qed.

Lemma block_ok_yz :
forall b x y z,
thread_set_2yz (S x) y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList y (fun j => (buildList z (fun k => b x j k)))).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. rewrite block_ok_z. rewrite IHy. reflexivity.
Qed.

Lemma block_ok_xz :
forall b x y z,
thread_set_2xz x (S y) z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList x (fun j => (buildList z (fun k => b j y k)))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. rewrite block_ok_z. rewrite IHx. reflexivity.
Qed.

Lemma block_ok_xy :
forall b x y z,
thread_set_2xy x y (S z) (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList x (fun j => (buildList y (fun k => b j k z)))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. rewrite block_ok_y. rewrite IHx. reflexivity.
Qed.

Lemma block_ok_xyz :
forall b x y z,
thread_set_3xyz x y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList x (fun i => (zip (buildList y (fun j => (buildList z (fun k => b i j k))))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y,z.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. rewrite empty_list. reflexivity. reflexivity. rewrite empty_list. simpl. rewrite empty_list in IHx. apply IHx. reflexivity. reflexivity.
      * simpl. rewrite block_ok_z. rewrite block_ok_yz. rewrite IHx. reflexivity.
Qed.

Lemma block_ok_yxz :
forall b x y z,
thread_set_3yxz x y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList y (fun j => (zip (buildList x (fun i => (buildList z (fun k => b i j k))))))).
Proof.
  induction y.
    + intros. destruct x; reflexivity.
    + intros. simpl in *.
    destruct x,z.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. rewrite empty_list. reflexivity. reflexivity. rewrite empty_list. simpl. rewrite empty_list in IHy. apply IHy. reflexivity. reflexivity.
      * simpl. rewrite block_ok_z. rewrite block_ok_xz. rewrite IHy. simpl. reflexivity.
Qed.

Lemma block_ok_zxy :
forall b z x y,
thread_set_3zxy x y z (fun x0 : ThreadId_t => x0 :: []) b =
zip (buildList z (fun k => (zip (buildList x (fun i => (buildList y (fun j => b i j k))))))).
Proof.
  induction z.
    + intros. destruct x,y; reflexivity.
    + intros. simpl in *.
    destruct x,y.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. rewrite empty_list. reflexivity. reflexivity. rewrite empty_list. simpl. rewrite empty_list in IHz. apply IHz. reflexivity. reflexivity.
      * simpl. rewrite block_ok_y. rewrite block_ok_xy. rewrite IHz. simpl. reflexivity.
Qed.

Lemma grid_ok_z :
forall g x y z x' y' z',
thread_set_1z (S x) (S y) z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g x y k))).
Proof.
  induction z.
    + intros. reflexivity.
    + intros. simpl. rewrite IHz. reflexivity.
Qed.

Lemma grid_ok_y :
forall g x y z x' y' z',
thread_set_1y (S x) y (S z)
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList y (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g x k z))).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl. rewrite IHy. reflexivity.
Qed.

Lemma grid_ok_yz :
forall g x y z x' y' z',
thread_set_2yz (S x) y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList y (fun j => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g x j k))))).
Proof.
  induction y.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * intros. simpl. clear. induction y. reflexivity. apply IHy.
      * intros. simpl. rewrite grid_ok_z. rewrite IHy. reflexivity.
Qed.

Lemma grid_ok_xz :
forall g x y z x' y' z',
thread_set_2xz x (S y) z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList x (fun j => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g j y k))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct z.
      * intros. simpl. clear. induction x. reflexivity. apply IHx.
      * intros. simpl. rewrite grid_ok_z. rewrite IHx. reflexivity.
Qed.

Lemma grid_ok_xy :
forall g x y z x' y' z',
thread_set_2xy x y (S z)
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList x (fun j => zip (buildList y (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g j k z))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y.
      * intros. simpl. clear. induction x. reflexivity. apply IHx.
      * intros. simpl. rewrite grid_ok_y. rewrite IHx. reflexivity.
Qed.

Lemma grid_ok_yxz :
forall g y x z x' y' z',
thread_set_3yxz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList y (fun j => zip (buildList x (fun i => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k))))))).
Proof.
  induction y.
    + intros. destruct x; reflexivity.
    + intros. simpl in *.
    destruct x,z.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. reflexivity. apply IHy.
      * simpl. clear. induction y. rewrite empty_list. reflexivity. reflexivity. rewrite empty_list. simpl. rewrite empty_list in IHy. apply IHy. reflexivity. reflexivity.
      * simpl. rewrite grid_ok_z. rewrite grid_ok_xz. rewrite IHy. reflexivity.
Qed.

Lemma grid_ok_xyz :
forall g x y z x' y' z',
thread_set_3xyz x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList x (fun i => zip (buildList y (fun j => zip (buildList z (fun k : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k))))))).
Proof.
  induction x.
    + intros. reflexivity.
    + intros. simpl in *.
    destruct y,z.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. reflexivity. apply IHx.
      * simpl. clear. induction x. rewrite empty_list. reflexivity. reflexivity. rewrite empty_list. simpl. rewrite empty_list in IHx. apply IHx. reflexivity. reflexivity.
      * simpl. rewrite grid_ok_z. rewrite grid_ok_yz. rewrite IHx. reflexivity.
Qed.

Lemma grid_ok_zxy :
forall g z x y x' y' z',
thread_set_3zxy x y z
          (fun b : nat -> nat -> nat -> ThreadId_t =>
           thread_set_3xyz x' y' z' (fun x : ThreadId_t => x :: []) b) g = 
zip (buildList z (fun k => zip (buildList x (fun i => zip (buildList y (fun j : nat =>
         thread_set_3xyz x' y' z' (fun x0 : ThreadId_t => x0 :: []) (g i j k))))))).
Proof.
  induction z.
    + intros. destruct x,y; reflexivity.
    + intros. simpl in *.
    destruct x,y.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. reflexivity. apply IHz.
      * simpl. clear. induction z. rewrite empty_list. reflexivity. reflexivity. rewrite empty_list. simpl. rewrite empty_list in IHz. apply IHz. reflexivity. reflexivity.
      * simpl. rewrite grid_ok_y. rewrite grid_ok_xy. rewrite IHz. reflexivity.
Qed.


