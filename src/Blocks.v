Require Bool.
(* 

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
  (* 
     The id only purpose is to bring us the ability to talk about 
   different blocks.
   *)
  | NewBlock {n} (oldBlock : Block n) (id:nat) : Block (S n).

Definition AnyBlock := {n & Block n}.
(*
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


Lemma eqb_implies_same_nat {n m} (block1: Block n) (block2: Block m) : eqb block1 block2 = true -> n = m .
Admitted.
(*
Proof.
  intros H.
  induction block1.
  - destruct block2.
    + reflexivity.
    + discriminate H.
  - destruct block2.
    + discriminate H.
    + simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      apply eqb_eq_nat in H1.
      rewrite H1.
      specialize (IHblock1 _ H2).
      rewrite IHblock1.
      reflexivity.
Qed.
Proof.
  intros H.
  destruct (Nat.eqb n m) eqn:E.
  - apply eqb_eq_nat in E. 
    assumption.
  - destruct block1, block2; simpl in H; try discriminate H
    + auto.
    (* this is the special case, we can't just discriminate *)
    + assert (Nat.eqb n n0 = false) as not_successor.
      auto.
      rewrite not_successor in H. 
      discriminate H.
Qed.
*)

Lemma eqb_eq {n} (block1 block2: Block n)  : eqb block1 block2 = true -> block1 = block2.
Admitted.


Definition get_block_number {n : nat} (block : Block n) : nat :=
  match block with
  | OriginBlock => 0
  | NewBlock _ _ => S n
  end.


(* 
  ` Prefix B B' ` in the paper is presented as ` B <=B' `
*)
Inductive Prefix : forall {n}, Block n -> forall {m}, Block m -> Type :=
  (* B <= B *)
  | Same : forall n (block : Block n), Prefix block block
  (* B <= B'  ->  B <= (b :: B') *)
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
  Admitted.
(* TODO: remove the admitted.*)
(*refine (@rect2 _ _ _ _ _); [now constructor | simpl].
  intros H.
  apply eqb_implies_same_nat in H  as M.
  apply eqb_eq in H.
  unfold eqb in H.
  destruct (Nat.eqb n m) eqn:n_eq_m.
  - apply eqb_eq_nat in n_eq_m.
  destruct block1, block2.
  + apply Same.
  + (* Case: block1 = OriginBlock, block2 = NewBlock oldBlock2 id2 *)
   discriminate H.
  + (* Case: block1 = NewBlock oldBlock1 id1, block2 = OriginBlock *)
   discriminate H.
  + (* Case: block1 = NewBlock oldBlock1 id1, block2 = NewBlock oldBlock2 id2 *)
    simpl in H.
    apply Bool.andb_true_iff in H.
    destruct H as [Hids Hrecur].

    rewrite n_eq_m in H.
    simpl in H.
    apply Same.
Qed.
 *)


Fixpoint is_prefix {n m} (block1 : Block n) (block2: Block m) : option (Prefix block1 block2) : Type.
Admitted.
(*  :=
  match block1, block2 with
    | OriginBlock, _ => Some (originBlock_is_always_prefix block2)
    | _, OriginBlock => None
    | NewBlock oldBlock1 _, NewBlock oldBlock2 _ =>
      if Nat.eqb n m then 
        let comparition := eqb block1 block2
        in
          if comparition then 
            let same_nat := eqb_implies_same_nat block1 block2
            in
            eqb_blocks_are_prefix block1 block2 comparition
          else 
            None
      else
        match is_prefix oldBlock1 oldBlock2 with
        | Some p => Some (IsPrefix block1 p)
        | None => None
        end
  end.
 *)

(*
  IsChildren B B' = B' < B
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
