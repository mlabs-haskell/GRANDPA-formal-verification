Require Coq.Vectors.Vector.


Definition Vector := VectorDef.t.
(* 
  
*)

Inductive Block : nat -> Type:= 
  | OriginBlock : Block 0
  | NewBlock {n} (oldBlock : Block n) (id:nat) : Block (S n).



(* 
  In the paper they constantly use B < B' as blocks, using the fact
   that a block contains the hash of it's predecessor. To facilitate 
   our lives, we replaced the hash of the previous block with the 
   entire Block-Chain. This isn't wise in a real implementation,
   but would simplify our proofs.
   This means that whenever the paper compares two blocks we would 
   replace the statement with a equivalent one comparing two 
   Chains.
   Additionally we are choosing Vectors to represent a chain of blocks 
   since we are only interested in two things: 
   - Block number (provided by the index of the block in the chain)
   - A way to have different blocks.
 *)

(* 
  This corresponds to head(C) <= head(C').
  There exits various ways to define this relation but we believe 
  that this one would be quite useful.
*)
Inductive Prefix : forall {n}, Block n -> forall {m}, Block m -> Type :=
  (* C <= C*)
  | Same : forall n (block : Block n), Prefix block block
  (* C <= C'  ->  C <= (B :: C')*)
  | IsPrefix {n m} (block1: Block n) (block2: Block m) (block_id : nat) :
      Prefix block1 block2 -> Prefix block1 (NewBlock block2 block_id).


(* 
   Is equivalent to the relation B ~ B' in the paper
   We express it like `(B <= B' ) /\ (B' <= B)` instead 
   of the one in the paper `B<B' /\ B=B! /\ B>B'` .

 *)
Variant Related : forall {n}, Block n -> forall {m}, Block m -> Prop :=
  | IsLower {n m } (block1:Block n) (block2:Block m) 
    : Prefix block1 block2 -> Related block1 block2
  | IsUpper {n m } (block1:Block n) (block2:Block m)  
    : Prefix block2 block1 -> Related block2 block1.

Definition Unrelated {n m} (block1 : Block n) (block2 :Block m) : Type := not (Related block1 block2).


