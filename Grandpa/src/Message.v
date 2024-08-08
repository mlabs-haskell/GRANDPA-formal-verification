Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import Voters.
Require Import Voter.
Require Import Vote.
Require Import Instances.Unit.
Require Import Dictionary.
Require Import Sets.
Require Import Time.
Require Import RoundNumber.

Require Import DataTypes.NatWrapper.
Export NatWrapper.

Require Import Coq.Arith.Arith.
Require Import List.

Require Import Classes.Eqb.

Variant MessageIdPhantom :=  MessageIdPhantomC.

Definition MessageId := NatWrapper MessageIdPhantom.

Definition from_nat := @NatWrapper.from_nat MessageIdPhantom.
Definition to_nat := @NatWrapper.to_nat MessageIdPhantom.


(**
  The evidence of the voter sending the message 
   to include the block as finalized.

  A byzantine voter may send anything.
*)
Record FinalizeBlock :Type 
  :=
  {
    prevoters: Voters
    ;precommiters: Voters
    ;prevotes : Votes prevoters
    ;precommits : Votes precommiters
  }.




(**
  The FinalizationMessage inducles a parameter as a hack to 
   store the voter evidence.
*)
Variant MessageKind : Type
  :=
  | PreCommitMessage : MessageKind
  | PreVoteMessage : MessageKind
  | EstimateMessage: MessageKind
  | FinalizationMessage (votes:FinalizeBlock) : MessageKind.

(**
In a real implementation we may distinguish messages by the 
id of the voter is sending it and another id related to it 
(maybe they mantain their own or we use a hash).

Whoever our model runs in a single machine and allow us to 
maintain the notion of _the total number of messages emitted_ .

The message include all the information to recognize who send it,
at what time was send and the round at witch this message correspond.

For messages we maintain a single global collection storing all the 
messages that haven't been received by all voters. 

We attempt to deliver a message to all the participants that haven't receive it 
before we start a step in the main model loop. 
As such, every message stores the set of voters that have received it until now.

Whenever a message [processed_by] field contains all the protocol participants, 
we delete the message from the global collection of messages.
*)

Record Message :=
   { id:MessageId
    ;block:AnyBlock
    ;kind: MessageKind
    ;round:RoundNumber
    ;time:Time
    ;voter:Voter
    ;processed_by:Sets.DictionarySet Voter
   }.

Definition update_message_proccessed (msg:Message) (v:Voter) := 
  {|
    id:=msg.(id)
    ;block:=msg.(block)
;kind := msg.(kind)
;round:=msg.(round)
    ;time:=msg.(time)
    ;voter:=msg.(voter)
    ;processed_by:= Sets.add v msg.(processed_by)
  |}.



Lemma message_to_vote_aux (msg:Message) 
  (voters: Voters)
  : option (Vote voters).
Proof.
  destruct msg eqn:msg_eq.
  pose (List.find (eqb voter0) (Voters.to_list voters)) as find_eq.
  destruct find_eq eqn:find_is.
  2: refine None.
  subst find_eq.
  apply (List.find_some _ _ )in find_is.
  destruct find_is as [in_proof is_voter].
  rewrite eqb_eq in is_voter.
  rewrite <- is_voter in in_proof.
  refine (Some(VoteC _ msg.(block).(AnyBlock.block_number) msg.(block).(AnyBlock.block) voter0 in_proof )).
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

