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
  io_bizantine_vote : Time -> Voter -> option AnyBlock;
  io_bizantine_advance_round : Time -> Voter-> nat -> bool;
  io_get_round_voters:  nat -> Dictionary.Dictionary nat VoterKind;
  (*TODO: add an Io that returns all time participants and use in initialization*)
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

Definition voter_is_primary_for_round `{Io} (v:Voter) (round_number:nat):bool
  := 
  io_get_round_primary round_number =? v.

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

Definition get_round_total_voters `{Io} (round_number:nat)
  : nat
  := 
    length (Dictionary.to_list (io_get_round_voters round_number)).

Definition get_round_bizantiners_number `{Io} (round_number:nat)
  : nat
  := 
  match process_round_voters round_number with
  | (bizantiners_number, _, _) 
    => bizantiners_number
  end.

Definition init_next_round_voter_state `{Io}
  (time:Time)
  (vs:VoterState)
  :VoterState 
  := 
  let round_number := S vs.(VoterState.round_number)
  in
  let total_voters := get_round_total_voters round_number
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
    let rounds : Vectors.Vec OpaqueRound.OpaqueRoundState (S round_number)
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
      ;pending_messages 
        := vs.(pending_messages)
      ;finalized_blocks := vs.(finalized_blocks)
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

Definition advance_count (state:State) : State :=
  {|
    message_count:=S state.(message_count)
    ;pending_messages:= state.(pending_messages)
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

Definition make_initial_state `{Io}
  :State
  :=
  let as_list :=Dictionary.to_list (io_get_round_voters 0) 
  in
  let total_voters := length as_list
  in
  match process_round_voters 1 with
  | (bizantiners_number, prevote_voters_list, precommit_voters_list) 
    =>
    let prevote_voters 
      := Votes.voters_from_list prevote_voters_list total_voters
    in
    let precommit_voters 
      := Votes.voters_from_list precommit_voters_list total_voters
    in
    let
      init_vs  := VoterState.make_initial_voter_state prevote_voters precommit_voters
    in
    {|
      message_count:=0
      ;pending_messages:= Dictionary.empty
      ;voters_state
        := 
        Dictionary.from_list Nat.eqb (map (fun x =>(fst x,init_vs)) as_list) 
      ;commited_blocks:= (Blocks.to_any OriginBlock,0,0)::nil
    |}
  end.

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

Definition build_and_send_prevote
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= S state.(message_count)
          ;Message.block:=b
          ;kind:=Message.PreVoteMessage
          ;round:=vs.(VoterState.round_number)
          ;time:=t
          ;voter:=voter
          ;processed_by:=Dictionary.from_list Nat.eqb ((voter,UnitC)::List.nil)
        |}
      in
        let 
          up_prevote := VoterState.update_prevoted vs (Some b)
        in
        let up_round := VoterState.update_votes_with_msg up_prevote new_message
        in 
        advance_count
          (update_voter_state (update_message state new_message) voter up_round).

Definition build_and_send_precommit
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= S state.(message_count)
          ;Message.block:=b
          ;kind:=Message.PreCommitMessage
          ;round:=vs.(VoterState.round_number)
          ;time:=t
          ;voter:=voter
          ;processed_by:=Dictionary.from_list Nat.eqb ((voter,UnitC)::List.nil)
        |}
      in
        let 
          up_precommit := VoterState.update_precommit vs (Some b)
        in
        let up_round := VoterState.update_votes_with_msg up_precommit new_message
        in 
        advance_count
          (update_voter_state (update_message state new_message) voter up_round).

Definition build_and_send_primary_estimate
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= S state.(message_count)
          ;Message.block:=b
          ;kind:=Message.EstimateMessage
          ;round:=vs.(VoterState.round_number)
          ;time:=t
          ;voter:=voter
          ;processed_by:=Dictionary.from_list Nat.eqb ((voter,UnitC)::List.nil)
        |}
      in
      let updated_voter_state
        := 
        VoterState.update_last_block vs b
      in
        advance_count
          (update_voter_state 
            (update_message state new_message) 
            voter updated_voter_state
          ).

Definition build_and_send_finalized_block
  (t:Time)
  (state:State) 
  (voter:Voter) 
  (vs:VoterState)
  (b:AnyBlock)
  (votes:Message.FinalizeBlock)
  :State
  :=
      let new_message : Message.Message 
        :=
        {| 
          id:= S state.(message_count)
          ;Message.block:=b
          ;kind:=Message.FinalizationMessage votes
          ;round:=vs.(VoterState.round_number)
          ;time:=t
          ;voter:=voter
          ;processed_by:=Dictionary.from_list Nat.eqb ((voter,UnitC)::List.nil)
        |}
      in
      let updated_voter_state
        := 
        VoterState.update_add_finalized_block vs b
      in
        advance_count
          (update_voter_state 
            (update_message state new_message) 
            voter updated_voter_state
          ).


Definition prevoter_step_aux `{Io} (t:Time) (state:State) (voter:Voter) (vs:VoterState)
  :State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower (vs.(VoterState.round_number)-1) with
  |Some (OpaqueRound.OpaqueRoundStateC previous_round)
    => 
    let ref_block := 
      match vs.(last_brodcasted_block) with
      | Some b => 
          match 
            (g (get_all_prevote_votes previous_round)
              ,get_estimate previous_round
            )
          with
          | (Some g_prev, Some estimate_prev)
              =>
              if 
                is_prefix (projT2 estimate_prev) (projT2 b) 
                && is_prefix (projT2 b) (projT2 g_prev)
              then Some b
              else get_estimate previous_round
          | _ => get_estimate previous_round
          end
      | None => get_estimate previous_round
      end
    in 
    match map (look_for_best_chain_for_block t voter) ref_block with 
    | Some b => build_and_send_prevote t state voter vs b
    | None => state
    end
  | None => state
  end.

Definition prevoter_step_legit `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  match vs.(prevoted_block) with 
  | Some _ => state 
  | None =>
    let tower := vs.(VoterState.rounds)
    in
    match Vectors.get tower vs.(VoterState.round_number) with
    | Some (OpaqueRound.OpaqueRoundStateC round_) =>
      match try_to_complete_round round_  with
      | Some _ => 
          prevoter_step_aux t state voter vs
      | None=>
          if t<=? Round.get_start_time round_ + 2*global_time_constant 
          then 
            prevoter_step_aux t state voter vs
          else
            state
      end
    (*This shouldn't happen!*)
    | None => state
    end
  end.

Definition prevoter_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  match category with 
  | VoterState.Bizantine 
    =>
    match io_bizantine_vote t voter with 
    | Some b => build_and_send_prevote t state voter vs b
    | None => state
    end
  | VoterState.Honest 
    => 
    prevoter_step_legit t state voter category vs
  end.

Definition precommit_step_legit `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match vs.(precommited_block) with 
  | Some _ => state
  | None =>
    match Vectors.get tower vs.(VoterState.round_number) with
    | Some (OpaqueRound.OpaqueRoundStateC r) =>
      match Vectors.get tower (vs.(VoterState.round_number)-1) with
      | Some (OpaqueRound.OpaqueRoundStateC r_prev) =>
        match (g (get_all_prevote_votes r), get_estimate r_prev) with 
        | (Some g_r,Some estimate_prev)
          => 
          (* TODO: add third condition of precommit *)
          if (t <? get_start_time r + 4*global_time_constant)
            || Estimate.is_completable r 
          then
            build_and_send_precommit t state voter vs g_r 
          else 
            state 
        | _ => state
        end
      | None => state
      end
    (*This shouldn't happen!*)
    | None => state
    end
  end.

Definition precommit_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  match category with 
  | VoterState.Bizantine 
    =>
    match io_bizantine_vote t voter with 
    | Some b => 
        build_and_send_precommit t state voter vs b
    | None => state
    end
  | VoterState.Honest 
    => 
    precommit_step_legit t state voter category vs
  end.

Definition get_last_finalized_block_number
  (finalized_blocks:Sets.DictionarySet AnyBlock)  
  : nat
  := 
  List.fold_left 
    (fun acc y => max acc (projT1 y)) 
    (Sets.to_list finalized_blocks)
    0.

Definition should_finalize
  (finalized_blocks:Sets.DictionarySet AnyBlock)  
  (opaque:OpaqueRound.OpaqueRoundState) 
  : option AnyBlock
  :=
  let max_block_number := get_last_finalized_block_number finalized_blocks
  in
  match opaque with 
  | OpaqueRound.OpaqueRoundStateC r 
    =>
    match g (Round.get_all_precommit_votes r) with
    | None => None
    | Some b => 
      if negb 
        (Sets.or
          (fun b2 
            => 
            ((projT1 b) <? max_block_number)
            ||
            is_prefix (projT2 b) (projT2 b2)
          ) 
          finalized_blocks
        )
      then 
        Some b 
      else None
    end
  end.


Definition is_some {A} (o:option A) : bool
  := 
  match o with 
  | Some _ => true
  | _ => false
  end.

Definition get_voter_kind_for_round `{Io} (v:Voter) (round_number:nat)
  :option VoterKind
  :=
  Dictionary.lookup  Nat.eqb v (io_get_round_voters round_number).

Definition get_voter_state (v:Voter) (state:State)
  :option VoterState
  :=
  Dictionary.lookup  Nat.eqb v state.(voters_state) .

Definition is_voter_for_round `{Io} (v:Voter) (round_number:nat)
  : bool
  := 
  is_some (get_voter_kind_for_round v round_number).

Program Definition get_blocks_to_finalize `{Io} (voter:Voter) (vs:VoterState) 
  : list (OpaqueRound.OpaqueRoundState * AnyBlock)
  := 
  let finalizeds := vs.(VoterState.finalized_blocks)
  in
  let all_previous_rounds 
    : list OpaqueRound.OpaqueRoundState
    := 
    (
      VectorDef.to_list 
        (
          VectorDef.take 
            (vs.(VoterState.round_number)-1) 
            _ 
            vs.(VoterState.rounds)
        )
    )
  in
  let predicate
    : OpaqueRound.OpaqueRoundState -> bool
    :=fun opaque => is_voter_for_round voter (OpaqueRound.get_round_number opaque)
  in
  let filtered_rounds 
    : list OpaqueRound.OpaqueRoundState
    := List.filter predicate all_previous_rounds
  in
  List.fold_left 
    (fun acc opaque => 
      match should_finalize finalizeds opaque  with 
      | Some b => (opaque,b)::acc 
      | None => acc end
    ) 
    filtered_rounds
    List.nil.
Next Obligation.
  transitivity (round_number vs).
  rewrite PeanoNat.Nat.sub_1_r.
  apply PeanoNat.Nat.le_pred_l.
  apply PeanoNat.Nat.le_succ_diag_r.
Qed.

Definition finalize_block (t:Time) 
  (voter:Voter) 
  (state:State) 
  (opaque_and_block:OpaqueRound.OpaqueRoundState * AnyBlock)
  : State
  :=
  match get_voter_state voter state with
  | Some vs 
    => 
    let (opaque,b) := opaque_and_block
    in
    let fin_msg
      :Message.FinalizeBlock
      :={|
        prevoters:= OpaqueRound.get_prevote_voters opaque
        ;precommiters:= OpaqueRound.get_precommit_voters opaque
        ;prevotes:= OpaqueRound.get_all_prevote_votes opaque
        ;precommits:= OpaqueRound.get_all_precommit_votes opaque
      |}
    in
    build_and_send_finalized_block t state voter vs b fin_msg
  | None => state
  end.
 

Definition finalization `{Io} (t:Time) (state:State) 
  (voter:Voter) (vs:VoterState) 
  :State 
  := 
  List.fold_left 
    (finalize_block t voter) 
    (get_blocks_to_finalize voter vs) 
    state.


Definition wait_step_for_new_round `{Io}
  (t:Time) 
  (voter:Voter) 
  (vs:VoterState)
  (state:State)
  : State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower (vs.(VoterState.round_number)) with
  |Some (OpaqueRound.OpaqueRoundStateC r)
    =>
    match try_to_complete_round r with
    | Some _ => 
        let new_vs := 
          init_next_round_voter_state t vs
        in
        let updated_state := update_voter_state state voter new_vs 
        in
        if voter_is_primary_for_round voter vs.(VoterState.round_number)
        then
          match get_estimate r with 
          | Some b => build_and_send_primary_estimate t state voter vs b
          | None => updated_state
          end
        else
          updated_state
    | None => state
    end
  | None => state
  end.

Definition should_wait_for_next_round `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter)
  (vs:VoterState)
  : bool
  :=
  match get_voter_kind_for_round voter vs.(VoterState.round_number) with
  | Some (VoterKindC Bizantine _) => 
      io_bizantine_advance_round t voter vs.(VoterState.round_number)
  | Some (VoterKindC _ vote_right) 
      =>
      match vote_right with 
      | VotePrevote
          => is_some vs.(VoterState.prevoted_block)
      | VotePrecommit
          => is_some vs.(VoterState.precommited_block)
      | VoteBoth
          => is_some vs.(VoterState.prevoted_block)
              &&
              is_some vs.(VoterState.precommited_block)
      end
  | None => true
  end.

Definition voter_round_step_aux `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match get_voter_state voter state with
  | Some voter_state_ =>  
      if should_wait_for_next_round t state voter voter_state_ 
      then wait_step_for_new_round t voter voter_state_ state
      else
        match 
          get_voter_kind_for_round voter voter_state_.(VoterState.round_number)
        with
        | Some(VoterKindC category kind_) => 
            match kind_ with
            | VotePrevote 
                => 
                prevoter_step t state voter category voter_state_
            | VotePrecommit 
                =>  
                precommit_step t state voter category voter_state_
            | VoteBoth => 
                match voter_state_.(VoterState.prevoted_block) with
                | Some _ => 
                  match voter_state_.(VoterState.precommited_block) with
                  (* this shouldn't happen! thanks to the first check *)
                  |Some _ => state
                  |None =>
                    precommit_step t state voter category voter_state_
                  end
                | None => 
                  prevoter_step t state voter category voter_state_
                end
            end
        | _ => state 
        end
  (*This shouldn't happen, we set all participants at the begining!*)
  | _ => state
  end.

Definition voter_round_step `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match Dictionary.lookup Nat.eqb voter state.(voters_state)with
  | Some vs =>  
    voter_round_step_aux 
      t 
      (finalization t state voter vs)
      voter
  | None => state
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
  get_last t (produce_states 0 make_initial_state). 

(* Compute get_state_up_to 1. *)


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

Section ProtocolConsistency.

Definition get_voter_opaque_round (state:State) (v:Voter) (t:Time) (r_n:nat)
  : option OpaqueRound.OpaqueRoundState 
  := 
  match (Dictionary.lookup Nat.eqb v (voters_state state)) with
  |None => None
  | Some vs => Vectors.get vs.(VoterState.rounds) r_n 
  end.

Lemma voter_state_continuos_existence `{Io}
  (v:Voter)
  (t: Time)
  (r_n:nat)
  (
    is_some_at_t
    : exists vs1
      , Dictionary.lookup 
        Nat.eqb 
        v 
        (voters_state (get_state_up_to t)) = Some vs1
  )
  (t_increment:Time)
    : exists vs2
      , Dictionary.lookup 
        Nat.eqb 
        v 
        (voters_state (get_state_up_to (t_increment+t)%nat )) = Some vs2.
Proof.
  dependent induction t_increment. 
  - eauto.
  - destruct IHt_increment as [r2 is_some_at_tinc].
    unfold get_state_up_to.
    unfold get_last.
    Admitted.

Lemma round_continuos_existence `{Io}
  (v:Voter)
  (t: Time)
  (r_n:nat)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    : get_voter_opaque_round (get_state_up_to t) v t r_n = Some r1
  )
  (t_increment:Time)
    : exists r2
    , get_voter_opaque_round (get_state_up_to (t_increment+t)%nat) v (t_increment+t)%nat r_n = Some r2.
Proof.
  dependent induction t_increment. 
  - eauto.
  - destruct IHt_increment as [r2 is_some_at_tinc].
    unfold get_voter_opaque_round.
  Admitted.

Lemma round_prevoters_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:nat)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :get_voter_opaque_round (get_state_up_to t) v t r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  get_voter_opaque_round 
    (get_state_up_to (t_increment+t)%nat )
    v 
    (t_increment+t)%nat
    r_n 
    = Some r2 
  /\ (OpaqueRound.get_prevote_voters r2 = OpaqueRound.get_prevote_voters r1).
Proof.
  destruct (round_continuos_existence v t r_n r1 is_some_at_t t_increment)
    as [r2 is_some].
  exists r2.
  split.
  apply is_some.
  induction t_increment.
  - simpl in is_some.
    rewrite is_some in is_some_at_t.
    injection is_some_at_t.
    intro eq_r.
    rewrite  eq_r.
    reflexivity.
  - Admitted.



(*
Lemma votes_are_monotone_over_time `{Io}
  (v:Voter)
  (t1 t2:Time)
  (r_n:nat)
  (related_t:t1 <= t2)
  (state_is_from_protocol: get_state_up_to t)
  (b_in
    :List.In 
      (to_any b) 
      (List.map ( fun x => fst (fst x)) (commited_blocks state))
  )
  .
*)

Lemma commits_came_from_voter {n:nat} (b:Block n) 
  {t:Time}
  `{Io}
  (state:State)
  (state_is_from_protocol: state =  get_state_up_to t)
  (b_in
    :List.In 
      (to_any b) 
      (List.map ( fun x => fst (fst x)) (commited_blocks state))
  )
  :
  exists (r_n:nat) (v:Voter) tv pv_v pc_v t0 t' 
    (r:RoundState tv pv_v pc_v t0 r_n t')
    , get_voter_opaque_round state v t r_n
      = Some (OpaqueRound.OpaqueRoundStateC r)
    /\ 
      g 
        (get_all_precommit_votes 
          (
          total_voters:= Round.get_total_voters r
          ) r
        ) = Some (to_any b).
Proof.
  remember (to_any b) as ab eqn:ab_eq_b.
  apply in_map in b_in.
  destruct b_in as [ [[b_send t_send] r_n ] [ab_eq_send in_commits] ].
  exists r_n.
  Admitted.

  
End ProtocolConsistency.

(* TODO: Correct bizantiners number*)
Theorem theorem_4_1 {n1 n2 bizantine_number:nat} (b1:Block n1) (b2:Block n2) 
  (un_related:Unrelated b1 b2)
  (state:State)
  {t:Time}
  `{Io}
  (state_is_from_protocol: state =  get_state_up_to t)
  (b1_in:List.In (to_any b1) (List.map ( fun x => fst (fst x)) (commited_blocks state)))
  (b2_in:List.In (to_any b2) (List.map ( fun x => fst (fst x)) (commited_blocks state)))
  : exists r b (s:Sets.DictionarySet Voter), 
    (
      (length (Sets.to_list s) >= bizantine_number +1) 
      /\
      (forall v, List.In v (Sets.to_list s) -> voted v r state b)
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
    + 
Admitted.
(*    + Search List.In. *)
      (* List.in_split*)
      (* List.in_map*)
(* if n < n0 *)


(*
Corollary corollary_4_3 
  `{Io}
  (t:Time)
  (bizantiners_restriction
    :
    forall r_n,
    get_round_bizantiners_number r_n < (get_round_total_voters r_n) /3
  )
  (b:AnyBlock)
  (r_n:nat)
  (finalized_at: exists t2, List.In (b,r_n,t2) (commited_blocks (get_state_up_to t))  )
  (v:Voter)
  (*TODO: fix this*)
  (is_honest:nat)
  (r_difference:nat)
  (is_completable:nat (*get_state_up_to t*))
  :nat.
*)

Close Scope type_scope.
