Require Import Blocks.                 
Require Import Votes.                  
Require Import Preliminars.
Require Import Round.
Require Import Estimate.
Require Import VoterState.

Require Import Message.

Require Import Functors.
Require Import Vectors.
Require Import Sets.

Require Import Nat.
Require Import Program.Equality.
(*Require Arith.Compare_dec.
 *)

Class Io := {
  global_time_constant: nat;
  block_producer (time voter:nat) : 
    Sets.DictionarySet AnyBlock;
  io_accept_vote : Time -> Message -> Voter -> bool;
  (* the nat is the round number*)
  io_get_round_voters:  nat -> Dictionary.Dictionary nat VoterKind;
  io_get_round_primary : nat -> Voter;
  (*TODO: add more restrictions to the block producer:
     - If v1 sees block b at t1 then all other v see b at t1+T
     - if v sees block b at t1, then 
         v sees b at t1+ t2 forall t2
  *)
  block_producer_not_emtpy 
  :forall t v, Sets.is_empty (block_producer t v) = false;
  primary_consistent 
    : forall r , 
        List.In 
        (io_get_round_primary r) 
        (List.map fst (Dictionary.to_list (io_get_round_voters r )));
}.

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

Definition process_round_voters `{Io} (r:nat)
  : (nat*list Voter *list Voter)
  :=
  let as_list :=Dictionary.to_list (io_get_round_voters r) 
  in
  List.fold_left process_round_voters_step as_list ((0,List.nil,List.nil)).

Definition init_next_round_voter_state `{Io}
  (time:Time)
  (vs:VoterState)
  :VoterState 
  := 
  let round_number := S vs.(VoterState.round_number)
  in
  let as_list :=Dictionary.to_list (io_get_round_voters round_number) 
  in
  let total_voters := length as_list
  in
  match process_round_voters round_number with
  | (bizantiners_number, prevote_voters_list, precommit_voters_list) 
    =>
    let prevote_voters 
      := Votes.voters_from_list prevote_voters_list total_voters
    in
    let precommit_voters 
      := Votes.voters_from_list precommit_voters_list total_voters
    in
    let round := 
      OpaqueRound.OpaqueRoundStateC(
        InitialRoundState 
          total_voters
          prevote_voters 
          precommit_voters 
          time
          round_number
      )
    in
    let rounds : Vectors.Vec OpaqueRound.OpaqueRoundState round_number
      := Coq.Vectors.VectorDef.cons _ round _ vs.(rounds)
    in
    let  voter_state 
      :=
      {|
      round_number := round_number
      ;prevoted_block := None
      ;precommited_block := None
      ;last_brodcasted_block := None
      ;rounds :=  rounds
      ;message_count :=  vs.(VoterState.message_count)
      ;pending_messages 
        := vs.(pending_messages)
      |}
    in
    (* We only process the pending messages for this round 
      In theory there shouldnt be previous messages,
       but if any, the main updater process of messages 
       would take care of them.
    *)
    match Dictionary.lookup Nat.eqb round_number vs.(pending_messages) with
    | Some pending =>
      List.fold_left 
        update_with_msg 
        pending
        voter_state
    | None => voter_state
    end
  end.

Record State :={
  message_count:nat
  (* The key nat in the Dictionary is the message id *)
  ;pending_messages:Dictionary.Dictionary nat Message 
  ;voters_state:Dictionary.Dictionary nat VoterState
  ;commited_blocks: list (AnyBlock * Time * nat)
  }.

Definition empty_state : State :=
  {|
    message_count:=0
    ;pending_messages:=Dictionary.empty
    ;voters_state:=Dictionary.empty
    ;commited_blocks := List.nil
  |}.


Definition update_message (state:State) (msg:Message) : State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=Dictionary.add Nat.eqb msg.(id) msg state.(pending_messages)
    ;voters_state:=state.(voters_state)
    ;commited_blocks:=state.(commited_blocks)
  |}.

Definition update_voter_state (state:State) (voter:Voter) (vs:VoterState) : State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=state.(pending_messages)
    ;voters_state:=Dictionary.add Nat.eqb voter vs state.(voters_state)
    ;commited_blocks:=state.(commited_blocks)
  |}.

Definition remove_message (state:State) (msg:Message): State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=Dictionary.delete Nat.eqb msg.(id) state.(pending_messages)
    ;voters_state:=state.(voters_state)
    ;commited_blocks:=state.(commited_blocks)
  |}.

Definition set_as_processed_by (v:Voter) (msg:Message) (state:State): State :=
  update_message state (Message.update_message_proccessed msg v).


Definition is_processed_by(state:State) (msg:Message) (v:Voter) : bool:= 
  match Dictionary.lookup Nat.eqb msg.(id) state.(pending_messages) with
  | Some _ => true
  | None => false
  end.

Definition accept_vote (state:State) (voter:Voter) (msg:Message): State :=
  match Dictionary.lookup Nat.eqb voter state.(voters_state)with
  | Some voter_state_ => 
    update_voter_state 
    state 
    voter 
    (VoterState.update_with_msg voter_state_ msg)
  (* None means that a message for participant outside of the simulation is tried *)
  (* we expect this to never happend*)
  | _ => state
  end.

Definition update_vote_for_voter `{Io} (t:Time) (voter:Voter) (state:State) (msg:Message) : State :=
  if is_processed_by state msg voter then  
    state 
  else 
    if io_accept_vote t msg  voter
    then
      accept_vote state voter msg
    else
        if Nat.leb t (msg.(Message.time)+ global_time_constant) || (voter =? msg.(Message.voter))
        then accept_vote state voter msg else state.

Definition upate_votes_for_voter `{Io} (t:Time) (state:State) (voter:Voter) : State :=
  let messages := List.map snd (Dictionary.to_list (pending_messages state))
  in
  let f := update_vote_for_voter t voter 
  in
    List.fold_left f messages state.


Definition prune_message `{Io} (state:State) (msg:Message) : State := 
  let round_participants := io_get_round_voters (Message.round msg)
  in
  if 
      List.fold_left 
        (fun acc v => andb acc (is_processed_by state msg v) ) 
        (List.map fst (Dictionary.to_list round_participants))
        true
  then
    remove_message state msg 
  else 
    state .

Definition prune_messages `{Io} (state:State): State:=
  List.fold_left prune_message (List.map snd (Dictionary.to_list state.(pending_messages)) ) state.

Definition update_votes `{Io} (t:Time) (state:State) : State:=
  let state_votes_updated
    := 
    List.fold_left 
      (upate_votes_for_voter t ) 
      (List.map fst (Dictionary.to_list state.(voters_state)))
      state 
  in
  prune_messages state_votes_updated.

Definition look_for_best_chain_for_block `{Io} (t:Time) (v:Voter) (ablock:AnyBlock)
  : AnyBlock
  :=
  let (block_number,block) := ablock
  in
  let available_blocks := block_producer t v
  in
    List.fold_left 
      (fun x y => if (projT1 x) <? (projT1 y) then y else x)
      (
        List.filter 
        (fun x => Blocks.is_prefix block (projT2 x)) 
        (Sets.to_list available_blocks)
      )
      (existT _ _ OriginBlock).
  

Definition prevoter_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower vs.(VoterState.round_number) with
  | Some (OpaqueRound.OpaqueRoundStateC round_) =>
    match try_to_complete_round round_  with
    | Some(completable) => 
        match Vectors.get tower (vs.(VoterState.round_number)-1) with
        |Some (OpaqueRound.OpaqueRoundStateC previous_round)
            => 
            let ref_block := 
              match vs.(last_brodcasted_block) with
              | Some b => Some b
              | None => get_estimate previous_round
              end
            in 
            match map (look_for_best_chain_for_block t voter) ref_block with 
            | Some b => 
              state
            | None => state
            end
        (*This shouldn't happen!*)
        | None => state
        end
    | None=> state
    end
  (*This shouldn't happen!*)
  | None => state
  end.


Definition precommit_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State.
Admitted.


Definition voter_round_step `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match Dictionary.lookup Nat.eqb voter state.(voters_state)with
  | Some voter_state_ =>  
      (*TODO: Insert primary logic here first!*)
      match 
        Dictionary.lookup 
          Nat.eqb 
          voter 
          (io_get_round_voters voter_state_.(VoterState.round_number)) 
      with
      | Some(VoterKindC category kind_) => 
          match kind_ with
          | VotePrevote => prevoter_step t state voter category voter_state_
          | VotePrecommit =>  precommit_step t state voter category voter_state_
          (* TODO: FIx this to really do both! *)
          | VoteBoth => prevoter_step t state voter category voter_state_
          end
      | _ => state 
      end
  (*This shouldn't happen, we set all participants at the begining!*)
  | _ => state
  (* TODO:
  - get current voter state 
  - look for it's kind, 
  - look for what it have done this round 
  - advance or wait and end step
  match state.(voters_state) 
  *)
  end.

Definition voters_round_step `{Io} (t:Time) (state:State): State :=
  let voters := List.map fst (Dictionary.to_list state.(voters_state))
  in 
    List.fold_left (voter_round_step t) voters state .



CoInductive CoList (T:Type) :Type :=
  | CoCons : T -> CoList T -> CoList T.

Fixpoint get_last {T} (n:nat) (colist:CoList T): T
  := 
  match n with 
  | 0 => match colist  with 
         | CoCons _ element _ =>
             element
          end
  | S m => match colist with 
          | CoCons _ _ remain => get_last m remain
          end
  end.


CoFixpoint produce_states `{Io} (t:Time) (state:State): CoList State :=
  let new_state := voters_round_step t (update_votes t state)
  in
    CoCons State new_state  (produce_states (t+1) new_state).


Definition get_state_up_to `{Io} (t:Time): State :=   
  get_last t (produce_states 0 empty_state). 

(*
Compute get_state_up_to 10. 
*)


Lemma get_commited_blocks_are_related (state:State)
  (b1 b2 : AnyBlock) 
  (b1_in 
    : List.In b1 (List.map ( fun x => fst (fst x)) state.(commited_blocks)))
  (b2_in 
    : List.In b2 (List.map ( fun x => fst (fst x)) state.(commited_blocks)))
  : Related (projT2 b1) (projT2 b2).
Admitted.

Definition voted (v:Voter) (r:nat) (state:State) (b:AnyBlock):Prop.
Admitted.




(* for some reason /\ is disabled as notation *)

Open Scope type_scope.

(* TODO add a time and a state number and state that the working state is the state given by produce_states *)
Theorem theorem_4_1 {n1 n2 bizantine_number:nat} (b1:Block n1) (b2:Block n2) 
  (un_related:Unrelated b1 b2)
  (state:State)
  (b1_in:List.In (to_any b1) (List.map ( fun x => fst (fst x)) (commited_blocks state)))
  (b2_in:List.In (to_any b2) (List.map ( fun x => fst (fst x)) (commited_blocks state)))
  : exists r b (d:Dictionary.Dictionary Voter Unit), 
    (
      (length (List.map fst (Dictionary.to_list d)) >= bizantine_number +1) 
      /\
      (forall v, List.In v (List.map fst (Dictionary.to_list d)) -> voted v r state b)
      /\ (b = to_any b1  \/  b = to_any b2)
    ).
Proof.
  dependent induction b1. 
  - pose (originBlock_is_always_prefix b2) as contra.
    apply (prefix_implies_related _ _) in contra.
    contradiction.
  - dependent destruction b2.
    +  pose (originBlock_is_always_prefix (NewBlock b1 id)) as contra.  
       apply (prefix_implies_related _ _) in contra.
       apply related_symmetric in contra.
       contradiction.
Admitted.
(*    + Search List.In. *)
      (* List.in_split*)
      (* List.in_map*)
(* if n < n0 *)
Close Scope type_scope.
