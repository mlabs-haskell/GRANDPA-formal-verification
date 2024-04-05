Require Bool.
(** 

  In the real implementation is unpractical to have the full
  history of the blockchain and instead a new block stores
  the hash of the last block. In our case storing the hash
  only would lead to complications, as so, we choose to 
  store the full chain of blocks.

  Blocks are indexed by it's index in the chain.

  Originally we used the Vector type in the Coq prelude, 
  but it complicates the requirement of the `Original` block.
*)

Inductive Block : nat -> Type:= 
  | OriginBlock : Block 0
  (** 
     The id only purpose is to bring us the ability to talk about 
   different blocks.
   *)
  | NewBlock {n} (oldBlock : Block n) (id:nat) : Block (S n).

Definition AnyBlock := {n & Block n}.
(** 
Example:
  Definition newBlock_1 : AnyBlock := existT (fun n => Block n) 1 (NewBlock OriginBlock 1).
  Check newBlock_1 : AnyBlock .
*)

Fixpoint eqb {n m} (block1:Block n) (block2:Block m) := 
  match block1, block2 with
  | OriginBlock, OriginBlock => true
  | NewBlock old1 id1, NewBlock old2 id2 => andb (Nat.eqb id1 id2) (eqb old1 old2)
  | _, _ => false
  end.

Definition any_block_eqb (b1 b2: AnyBlock) : bool
  := 
    match b1 , b2 with 
    | (existT _ n1 b1'), (existT _ n2 b2') => eqb b1' b2'
    end.

Lemma eqb_eq_nat {n m} : Nat.eqb n m = true <-> n = m.
Admitted.


Require Import Coq.Program.Equality.
Require Import Setoid.
Lemma eqb_implies_same_nat {n} (block1: Block n): forall m (block2: Block m), eqb block1 block2 = true -> n = m .
Proof.
  induction block1 as [|n block1 HInductive id1].
  - intros m block2 Hblock2.
    destruct block2.
    + reflexivity.
    + simpl in Hblock2. 
      discriminate.
  - intros m block2 Hblock2.
    destruct block2 as [| pre_m pre_block2 pre_id] eqn:eq_block2 .
    + simpl in Hblock2. 
      discriminate.
    + simpl in Hblock2.
      apply Bool.andb_true_iff in Hblock2.
      destruct Hblock2 as [_ same_children].
      pose (HInductive pre_m pre_block2 same_children) as same_number .
      rewrite same_number.
      trivial.
Qed.

Lemma eqb_eq {n} (block1: Block n)  : forall (block2:Block n), eqb block1 block2 = true -> block1 = block2.
Proof.
  induction block1 as [|n block1 HInductive id].
  - intros block2 Hblock2.
    dependent destruction block2.
    reflexivity.
  - intros block2  Hblock2. 
    dependent destruction block2.
    simpl in Hblock2.
    apply Bool.andb_true_iff in Hblock2.
    destruct Hblock2 as [same_id same_children].
    pose (HInductive _ same_children) as eq_b1_b2.
    rewrite eqb_eq_nat in same_id.
    rewrite same_id.
    rewrite eq_b1_b2.
    trivial.
Qed.

Definition get_block_number {n : nat} (block : Block n) : nat :=
  match block with
  | OriginBlock => 0
  | NewBlock _ _ => S n
  end.


(**  
   [Prefix B B'] in the paper is presented as [B <= B'].
*)
Inductive Prefix : forall {n}, Block n -> forall {m}, Block m -> Type :=
  (** [B <= B']*)
  | Same : forall n (block : Block n), Prefix block block
  (** [B <= B'  ->  B <= (b :: B')] *)
  | IsPrefix {n m} (block1: Block n) (block2: Block m) (block_id : nat) :
      Prefix block1 block2 -> Prefix block1 (NewBlock block2 block_id).

Lemma originBlock_is_always_prefix  {n} (block:Block n):  Prefix OriginBlock block.
Proof.
  induction block.
  - (* Case: block = OriginBlock *)
    apply Same.
  - (* Case: block = NewBlock oldBlock id *)
    apply IsPrefix.
    apply IHblock.
Qed.


Lemma eqb_blocks_are_prefix {n} (block1 block2: Block n): eqb block1 block2 = true -> Prefix block1 block2.
Proof.
  intro H.
  pose (eqb_eq block1 block2 H) as eq_blocks.
  rewrite eq_blocks.
  refine (Same n block2).
Qed.

Open Scope nat_scope.

Fixpoint is_prefix {n m} (block1 : Block n) (block2: Block m) : option (Prefix block1 block2) 
 :=
  if Nat.leb n  m then
    match block2 with
    | OriginBlock => 
        match block1 with 
        | OriginBlock => Some (Same 0 OriginBlock)
        | _ => None
        end
    | NewBlock old_block id =>
        match is_prefix block1 old_block with
        | Some p => Some (IsPrefix block1 old_block id p)
        | None => None
        end
    end
  else
  None.
 

(**
  [IsChildren B B' = B' < B]
 *)

Variant IsChildren {n m} (block1 :Block n) (block2: Block m) : Type :=
  | IsChildrenC (is_prefix: Prefix block2 block1) (block_number_is_above: n<m) :
      IsChildren block1 block2.


(* 
   Is equivalent to the relation B ~ B' in the paper
   We express it like `(B <= B' ) \/ (B' <= B)` instead 
   of the one in the paper `B<B' /\ B=B! /\ B>B'` .

 *)
Variant Related : forall {n}, Block n -> forall {m}, Block m -> Prop :=
  | IsLower {n m } (block1:Block n) (block2:Block m) 
    : Prefix block1 block2 -> Related block1 block2
  | IsUpper {n m } (block1:Block n) (block2:Block m)  
    : Prefix block2 block1 -> Related block2 block1.

Definition Unrelated {n m} (block1 : Block n) (block2 :Block m) : Type := not (Related block1 block2).
