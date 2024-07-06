Require Import Blocks.
Require Import Votes.
Require Import Dictionary.

Require Import Nat.
Require Import Coq.Arith.Arith.
Require Import List.

Variant MessageKind : Type
  :=
  | PreCommitMessage : MessageKind
  | PreViewMessage : MessageKind
  | EstimateMessage: MessageKind
  | FinalizationMessage: MessageKind.

Record Message :=
   { id:nat 
    ;block:{n & Block n}
    ;kind: MessageKind
    ;round:nat
    ;time:nat
    ;voter:Voter
    ;processed_by:Dictionary Voter Unit
   }.

Definition update_message_proccessed (msg:Message) (v:Voter) := 
  {|
    id:=msg.(id)
    ;block:=msg.(block)
;kind := msg.(kind)
;round:=msg.(round)
    ;time:=msg.(time)
    ;voter:=msg.(voter)
    ;processed_by:= Dictionary.add Nat.eqb msg.(id) UnitC msg.(processed_by)
  |}.



Lemma message_to_vote_aux (msg:Message) 
  {bizantiners_number last_block_number: nat} 
  (voters: Voters bizantiners_number )
  (last_block:Block last_block_number)
  : option (Vote voters last_block).
Proof.
  destruct msg eqn:msg_eq.
  pose (List.find (Nat.eqb voter0) (voters_to_list voters)) as find_eq.
  destruct find_eq eqn:find_is.
  2: refine None.
  subst find_eq.
  apply (find_some _ _ )in find_is.
  destruct find_is as [in_proof is_voter].
  rewrite Nat.eqb_eq in is_voter.
  rewrite <- is_voter in in_proof.
  destruct (is_prefix last_block (projT2 block0)) eqn:blocks_eq.
  2: refine None.
  apply is_prefix_implies_prefix in blocks_eq.
  refine (Some(VoteC _ last_block voter0 in_proof _ blocks_eq)).
Qed.
  
(* Expected to be used in messages with precommit votes*)
Definition message_to_precommit_vote (msg:Message) 
  {bizantiners_number last_block_number: nat} 
  (voters: Voters bizantiners_number )
  (last_block:Block last_block_number)
  : option(Vote voters last_block ) := 
  match msg.(kind) with
  | PreCommitMessage => message_to_vote_aux msg voters last_block
  | _ => None
  end.

Definition message_to_preview_vote (msg:Message) 
  {bizantiners_number last_block_number: nat} 
  (voters: Voters bizantiners_number )
  (last_block:Block last_block_number)
  : option(Vote voters last_block ) := 
  match msg.(kind) with
  | PreViewMessage => message_to_vote_aux msg voters last_block
  | _ => None
  end.

