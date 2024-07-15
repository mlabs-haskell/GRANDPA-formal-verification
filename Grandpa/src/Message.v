Require Import Blocks.
Require Import Votes.
Require Import Dictionary.
Require Import Sets.

Require Import Nat.
Require Import Coq.Arith.Arith.
Require Import List.

Record FinalizeBlock :Type 
  :=
  {
    prevoters: Voters
    ;precommiters: Voters
    ;prevotes : Votes prevoters
    ;precommits : Votes precommiters
  }.


Variant MessageKind : Type
  :=
  | PreCommitMessage : MessageKind
  | PreVoteMessage : MessageKind
  | EstimateMessage: MessageKind
  | FinalizationMessage (votes:FinalizeBlock) : MessageKind.

Record Message :=
   { id:nat 
    ;block:AnyBlock
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
    ;processed_by:= Dictionary.add Nat.eqb v UnitC msg.(processed_by)
  |}.



Lemma message_to_vote_aux (msg:Message) 
  (voters: Voters)
  : option (Vote voters).
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
  refine (Some(VoteC _ voter0 in_proof  (projT2 msg.(block)))).
Qed.
  
(* Expected to be used in messages with precommit votes*)
Definition message_to_precommit_vote (msg:Message) 
  (voters: Voters)
  : option(Vote voters) := 
  match msg.(kind) with
  | PreCommitMessage => message_to_vote_aux msg voters
  | _ => None
  end.

Definition message_to_prevote_vote (msg:Message) 
  (voters: Voters)
  : option(Vote voters) := 
  match msg.(kind) with
  | PreVoteMessage => message_to_vote_aux msg voters
  | _ => None
  end.

