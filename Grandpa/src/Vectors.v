Require Import Coq.Vectors.Vector.

Require Import Functors.

Definition Vec := Vector.t.

Definition coerce {A} {n} (v:Vec A n) : Coq.Vectors.VectorDef.t A n 
  := v.

Lemma aux_nat_to_fin (n:nat) (upper_bound:nat) 
  : option (Vectors.Fin.t upper_bound).
Proof.
  destruct (Vectors.Fin.of_nat n upper_bound).
  - refine (Some t).
  - refine None.
Qed.

Definition apply {A B} (sf : option (A -> B)) (mv : option A) 
  : option B
  :=
  match sf with
  | Some f =>  match mv with
    | Some v  => Some (f v) 
    | None => None
    end
  | None => None
  end.


Definition get {A} {length:nat} (v:Vec A length) (index:nat)
  : option A
  :=
  let maybe_index := aux_nat_to_fin index length 
  in
  map (Vector.nth  v) maybe_index.

(* 
  Out of bounds index is ignored
*)
Definition update {A}{length:nat} (v:Vec A length) (index:nat) (new_value:A)
  : Vec A length
  :=
  let maybe_index := aux_nat_to_fin index length 
  in
  match map (fun f => f new_value) (map (Vector.replace v) maybe_index) with
  | Some new_vec => new_vec
  | None => v
  end.
