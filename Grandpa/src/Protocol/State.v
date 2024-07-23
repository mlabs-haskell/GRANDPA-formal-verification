Require Import Blocks.AnyBlock.
Require Import DataTypes.Dictionary.
Require Import Message.
Require Import Votes.
Require Import VoterState.
Require Import Time.
Require Import RoundNumber.
Require Import Protocol.FinalizedBlock.

Require Import Classes.Functor.
Require Import Classes.Math.All.


Record State :={
  (**
    Mantains a global conunter of all messages emited until now.
    In a real implementation every voter should attach a ID 
    to their messages and that together with the voter ID 
    can be used as an id. We don't need to do that thanks to this.
  *)
  message_count:nat
  (**
    Messages that haven't been received by some voter yet.
  *)
  ;pending_messages:Dictionary MessageId Message 
  ;voters_state:Dictionary Voter VoterState
  (**
     All the blocks who any voter have finalized.
  *)
  ;global_finalized_blocks: list FinalizedBlock 
  }.

Section Update.

Definition empty_state : State :=
  {|
    message_count:=0
    ;pending_messages:=Dictionary.empty
    ;voters_state:=Dictionary.empty
    ;global_finalized_blocks := List.nil
  |}.

Definition update_message (state:State) (msg:Message) : State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=Dictionary.add msg.(id) msg state.(pending_messages)
    ;voters_state:=state.(voters_state)
    ;global_finalized_blocks:=state.(global_finalized_blocks)
  |}.

Definition advance_count (state:State) : State :=
  {|
    message_count:=S state.(message_count)
    ;pending_messages:= state.(pending_messages)
    ;voters_state:=state.(voters_state)
    ;global_finalized_blocks:=state.(global_finalized_blocks)
  |}.

Definition update_voter_state (state:State) (voter:Voter) (vs:VoterState) : State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=state.(pending_messages)
    ;voters_state:=Dictionary.add voter vs state.(voters_state)
    ;global_finalized_blocks:=state.(global_finalized_blocks)
  |}.

Definition remove_message (state:State) (msg:Message): State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=Dictionary.delete msg.(id) state.(pending_messages)
    ;voters_state:=state.(voters_state)
    ;global_finalized_blocks:=state.(global_finalized_blocks)
  |}.

End Update.

Section ProcessIo.
Open Scope list.

Definition process_round_voters_step 
  (acc: nat*(list Voter)*(list Voter) )
  (value:Voter*VoterKind)
  : (nat*list Voter *list Voter)
  :=
  match acc with
  | (bizantiners_number, prevote_voters, precommit_voters) 
    =>
    match value with
    | (voter,kind)
      =>
      match kind with
      | VoterKindC Bizantine VotePrevote 
          => (bizantiners_number+1, voter::prevote_voters,precommit_voters)
      | VoterKindC Bizantine VotePrecommit
          => (bizantiners_number+1, prevote_voters,voter::precommit_voters)
      | VoterKindC Bizantine VoteBoth
          => (bizantiners_number+1, voter::prevote_voters,voter::precommit_voters)
      | VoterKindC Honest VotePrevote 
          => (bizantiners_number, voter::prevote_voters,precommit_voters)
      | VoterKindC Honest VotePrecommit
          => (bizantiners_number,prevote_voters,voter::precommit_voters)
      | VoterKindC Honest VoteBoth 
          => (bizantiners_number, voter::prevote_voters,voter::precommit_voters)
      end
    end
  end.

Definition process_round_voters_from 
   (round_dictionary:Dictionary Voter VoterKind)
  : (nat*list Voter *list Voter)
  :=
  let as_list :=Dictionary.to_list round_dictionary
  in
  List.fold_left process_round_voters_step as_list ((0,List.nil,List.nil)).

Definition get_round_total_voters_from
  (round_dictionary:Dictionary Voter VoterKind)
  : nat
  := 
    List.length (Dictionary.to_list round_dictionary).

Definition get_round_bizantiners_number 
  (round_dictionary:Dictionary Voter VoterKind)
  : nat
  := 
  match process_round_voters_from round_dictionary with
  | (bizantiners_number, _, _) 
    => bizantiners_number
  end.

Definition make_initial_state_from 
  (round_zero_dict: Dictionary.Dictionary Voter VoterKind)
  (round_one_dict: Dictionary.Dictionary Voter VoterKind)
  :State
  :=
  let as_list :=Dictionary.to_list round_zero_dict
  in
  let total_voters := List.length as_list
  in
  match process_round_voters_from round_one_dict with
  | (bizantiners_number, prevote_voters_list, precommit_voters_list) 
    =>
    let prevote_voters 
      := Voters.from_list prevote_voters_list total_voters
    in
    let precommit_voters 
      := Voters.from_list precommit_voters_list total_voters
    in
    let
      init_vs  := VoterState.make_initial_voter_state prevote_voters precommit_voters
    in
    {|
      message_count:=0
      ;pending_messages:= Dictionary.empty
      ;voters_state
        := 
        Dictionary.from_list (map (fun x =>(fst x,init_vs)) as_list) 
      ;global_finalized_blocks:= 
        let origin_voters := Voters.from_list List.nil 0
        in
        {|
          FinalizedBlock.block := AnyBlock.to_any OriginBlock
          ;FinalizedBlock.time := Time.from_nat 0
          ;FinalizedBlock.round_number := RoundNumber.from_nat 0
          ;FinalizedBlock.submitter_voter:= Voter.from_nat 0
          ;FinalizedBlock.voters:= origin_voters
          ;FinalizedBlock.precommit_votes:= Votes.VotesC origin_voters List.nil
        |} :: List.nil
    |}
  end.

Open Scope math.
Definition init_next_round_voter_state_from 
  (round_dictionary: Dictionary Voter VoterKind)
  (time:Time)
  (vs:VoterState)
  :VoterState 
  := 
  let round_number : RoundNumber := ((RoundNumber.from_nat 1) + vs.(VoterState.round_number))%math
  in
  let total_voters := get_round_total_voters_from round_dictionary
  in
  match process_round_voters_from round_dictionary with
  | (bizantiners_number, prevote_voters_list, precommit_voters_list) 
    =>
    let prevote_voters 
      := Voters.from_list prevote_voters_list total_voters
    in
    let precommit_voters 
      := Voters.from_list precommit_voters_list total_voters
    in
    let round := 
      OpaqueRound.OpaqueRoundStateC(
        Round.InitialRoundState 
          total_voters
          prevote_voters 
          precommit_voters 
          time
          round_number
      )
    in
    let rounds : Vectors.Vec OpaqueRound.OpaqueRoundState ( 1 + RoundNumber.to_nat round_number )%math
      := Coq.Vectors.VectorDef.cons _ round _ vs.(rounds)
    in
    let  voter_state 
      :=
      {|
      VoterState.round_number := round_number
      ;prevoted_block := None
      ;precommited_block := None
      ;last_brodcasted_block := None
      ;rounds :=  rounds
      ;VoterState.pending_messages 
        := vs.(VoterState.pending_messages)
      ;VoterState.finalized_blocks := vs.(VoterState.finalized_blocks)
      |}
    in
    (* We only process the pending messages for this round 
      In theory there shouldnt be previous messages,
       but if any, the main updater process of messages 
       would take care of them.
    *)
    match Dictionary.lookup round_number vs.(VoterState.pending_messages) with
    | Some pending =>
      List.fold_left 
        update_with_msg 
        pending
        voter_state
    | None => voter_state
    end
  end.

End ProcessIo.


Definition get_voter_opaque_round (state:State) (v:Voter) (r_n:RoundNumber)
  : option OpaqueRound.OpaqueRoundState 
  := 
  match (Dictionary.lookup v (voters_state state)) with
  |None => None
  | Some vs => Vectors.get vs.(VoterState.rounds) (RoundNumber.to_nat r_n) 
  end.
