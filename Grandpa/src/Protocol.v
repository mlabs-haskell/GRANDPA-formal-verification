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

Require Import Lia.

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

Definition get_round_bizantine_voters `{Io} (round_number:nat)
  :list nat
  :=
  let f v_k :=
    match v_k with
    | (_,VoterKindC Bizantine _) => true
    | _ => false
    end
  in
  map fst  (List.filter f (Dictionary.to_list (io_get_round_voters round_number)) ).

Definition get_round_honest_voters `{Io} (round_number:nat)
  :list nat
  :=
  let f v_k :=
    match v_k with
    | (_,VoterKindC Honest _) => true
    | _ => false
    end
  in
  map fst  (List.filter f (Dictionary.to_list (io_get_round_voters round_number)) ).


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
  ;global_finalized_blocks: list (AnyBlock * Time * nat)
  }.

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
    ;pending_messages:=Dictionary.add Nat.eqb msg.(id) msg state.(pending_messages)
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
    ;voters_state:=Dictionary.add Nat.eqb voter vs state.(voters_state)
    ;global_finalized_blocks:=state.(global_finalized_blocks)
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
      ;global_finalized_blocks:= (Blocks.to_any OriginBlock,0,0)::nil
    |}
  end.

Definition remove_message (state:State) (msg:Message): State :=
  {|
    message_count:=state.(message_count)
    ;pending_messages:=Dictionary.delete Nat.eqb msg.(id) state.(pending_messages)
    ;voters_state:=state.(voters_state)
    ;global_finalized_blocks:=state.(global_finalized_blocks)
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

(* Compute get_state_up_to 0. *)


Lemma get_global_finalized_blocks_are_related (state:State)
  (b1 b2 : AnyBlock) 
  (b1_in 
    : List.In b1 (List.map ( fun x => fst (fst x)) state.(global_finalized_blocks)))
  (b2_in 
    : List.In b2 (List.map ( fun x => fst (fst x)) state.(global_finalized_blocks)))
  : Related (projT2 b1) (projT2 b2).
Admitted.


(* for some reason /\ is disabled as notation *)
Open Scope type_scope.

Section ProtocolConsistency.

Definition get_voter_opaque_round (state:State) (v:Voter) (r_n:nat)
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
    : get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
    : exists r2
    , get_voter_opaque_round (get_state_up_to (t_increment+t)%nat) v r_n = Some r2.
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
    :get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  get_voter_opaque_round 
    (get_state_up_to (t_increment+t)%nat )
    v 
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

Lemma round_precommiters_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:nat)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  get_voter_opaque_round 
    (get_state_up_to (t_increment+t)%nat )
    v 
    r_n 
    = Some r2 
  /\ (OpaqueRound.get_precommit_voters r2 = OpaqueRound.get_precommit_voters r1).
Admitted.

Lemma round_precomits_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:nat)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  (r2:OpaqueRound.OpaqueRoundState)
  (is_some_at_t_increment: 
    get_voter_opaque_round 
      (get_state_up_to (t_increment+t)%nat )
      v 
      r_n 
      = Some r2
  )
  (voters_are_equal: (OpaqueRound.get_precommit_voters r1) = (OpaqueRound.get_precommit_voters r2))
  : (Votes.castVotes voters_are_equal (OpaqueRound.get_all_precommit_votes r1) = OpaqueRound.get_all_precommit_votes r2).
Admitted.

Lemma finalized_blocks_monotone_over_time `{Io}
  (t:Time)
  (t_increment:Time)
  : exists  l, 
  (global_finalized_blocks (get_state_up_to (t_increment + t)%nat ))
  =
  l ++ (global_finalized_blocks (get_state_up_to t)).
Proof.
  Admitted.

Lemma finalized_blocks_monotone_over_time2 `{Io}
  (t:Time)
  (t_increment:Time)
  : forall b, List.In b (global_finalized_blocks (get_state_up_to t))
  ->
  List.In b (global_finalized_blocks (get_state_up_to (t_increment + t)%nat )).
Proof.
  Admitted.

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
      (List.map ( fun x => fst (fst x)) (global_finalized_blocks state))
  )
  .
*)

Lemma finalized_block_time_leq {n:nat} (b:Block n) 
  (r_n:nat)
  (t_n:Time)
  (t:Time)
  `{Io}
  (b_in
    :List.In 
      (to_any b,t_n, r_n )
       (global_finalized_blocks (get_state_up_to t))
  )
  : t_n <= t.
Admitted.

Lemma finalized_block_came_from_voter {n:nat} (b:Block n) 
  (r_n:nat)
  (t_n:Time)
  (t:Time)
  `{Io}
  (b_in
    :List.In 
      (to_any b, t_n, r_n )
       (global_finalized_blocks (get_state_up_to t))
  )
  :
  exists (v:Voter) 
    (r:OpaqueRound.OpaqueRoundState)
    , get_voter_opaque_round (get_state_up_to t_n) v r_n
      = Some r
    /\ 
      g 
        (OpaqueRound.get_all_precommit_votes 
          r
        ) = Some (to_any b).
Proof.
  remember (to_any b) as ab eqn:ab_eq_b.
  Admitted.


(*TODO: add consistency of total_number_of_voters param
  that is passed to both prevote and precommit set of voters for every round
*)
  
End ProtocolConsistency.


Definition VoterVotedInRound (v:Voter) (opaque:OpaqueRound.OpaqueRoundState)
  :Prop
  :=
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_prevote_votes opaque) = true)
    \/
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_precommit_votes opaque) = true).

Lemma theorem_4_1_eq_aux `{Io} 
  {n1 :nat} 
  (b1:Block n1) 
  (round_finalized :nat)
  (t1 :nat)
  (t:Time)
  (b1_in:List.In (to_any b1,t1, round_finalized) (global_finalized_blocks (get_state_up_to t)))
  : exists (v:Voter) (vr:OpaqueRound.OpaqueRoundState) (vr2:OpaqueRound.OpaqueRoundState)
  ,
    (
      get_voter_opaque_round (get_state_up_to t1) v round_finalized 
      =
      Some vr
    )
    /\
    (g (OpaqueRound.get_all_precommit_votes vr) = Some (to_any b1))
    /\
    (
      get_voter_opaque_round (get_state_up_to (t+2*global_time_constant)%nat) v round_finalized 
      = 
      Some vr2
    ).
Proof.
  pose (finalized_block_time_leq b1 round_finalized t1 t b1_in) as t1_leq_t.
  remember (t+2*global_time_constant)%nat as new_t eqn:new_t_eq.
  assert (List.In (to_any b1,t1, round_finalized) (global_finalized_blocks (get_state_up_to new_t))) as b1_in_new_t.
  {
    pose (finalized_blocks_monotone_over_time2 t (new_t - t) (to_any b1, t1,round_finalized) b1_in).
    enough ((new_t - t +t)%nat = new_t) as H0.
    rewrite <- H0.
    assumption.
    lia.
    }
  destruct (finalized_block_came_from_voter b1 round_finalized t1 new_t  b1_in_new_t) as [v [vr [is_some_vr g_vr]]].
  exists v.
  pose (round_continuos_existence v t1 round_finalized vr is_some_vr (new_t - t1)) as vr_exists_at_new_t.
  assert (new_t - t1 +t1 = new_t)%nat as is_new_t. lia.
  rewrite is_new_t in vr_exists_at_new_t.
  destruct vr_exists_at_new_t as [vr2 is_some_vr2].
  exists vr.
  exists vr2.
  auto.
Qed.


Lemma theorem_4_1_eq `{Io} 
  {n1 n2 :nat} 
  (b1:Block n1) 
  (b2:Block n2) 
  (round_finalized :nat)
  (t1 :nat)
  (t2 :nat)
  (un_related:Unrelated b1 b2)
  (t:Time)
  (b1_in:List.In (to_any b1,t1, round_finalized) (global_finalized_blocks (get_state_up_to t)))
  (b2_in:List.In (to_any b2,t2, round_finalized) (global_finalized_blocks (get_state_up_to t)))
  : exists (t3:Time) (v:Voter) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
    (
      (
        get_voter_opaque_round (get_state_up_to t3) v round_finalized = Some r
      )
      /\
      (
        length (Sets.to_list s) 
        >= 
        1+ Votes.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      ) 
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\ 
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters round_finalized))
    ).
Proof.
  remember (t + 2 * global_time_constant)%nat as new_t eqn:new_t_eq.
  exists new_t.
  destruct (theorem_4_1_eq_aux b1 round_finalized t1 t b1_in) as [v [v1r [v1r2 [is_some_v1r [g_v1r is_some_v1r2]]]]].
  exists v.
  exists v1r2.
  Search List.In.
  remember (List.filter (fun v3 => Votes.voter_voted_in_votes v3 (OpaqueRound.get_all_precommit_votes v1r2)) (get_round_bizantine_voters round_finalized)) as s_as_list eqn:s_as_list_eq.
  remember (Sets.from_list Nat.eqb s_as_list) as s.
  exists s.
  rewrite <- new_t_eq in is_some_v1r2.
  split.
  assumption.
  split.
  - destruct (theorem_4_1_eq_aux b2 round_finalized t2 t b2_in) as [v2 [v2r [v2r2 [is_some_v2r [g_v2r is_some_v2r2]]]]].
    (*
       TODO in 3.8 : 
       we need to show that after t+2*global_time_constant v has got all the votes on v2r, and as such we have 
       a supermajority for both blocks in this round (b1 and b2) at this time. 
       Then we destruct the Votes.is_safe predicate applied in the precommits at time t + 2*global_time_constant 
       In the False case, we end this sub-proof.
       In the True case, b_1 and b_2 are related by a lemma in the Votes.v about supermajority on safe sets, contra with un_related
    *)
  (*
    The other two parts to be proved, are a consequency of the construction of the list (literally they are in the predicate that build the list).
   *)
    Admitted.
  


Lemma theorem_4_1_lt `{Io} 
  {n1 n2 :nat} 
  (b1:Block n1) 
  (b2:Block n2) 
  (round_finalized_1 round_finalized_2:nat)
  (t1 t2:nat)
  (un_related:Unrelated b1 b2)
  (state:State)
  (t:Time)
  (state_is_from_protocol: state =  get_state_up_to t)
  (b1_in:List.In (to_any b1,t1, round_finalized_1) (global_finalized_blocks state))
  (b2_in:List.In (to_any b2,t2, round_finalized_2) (global_finalized_blocks state))
  (symmetry_hipotesis:round_finalized_1 < round_finalized_2)
  : exists (t3:Time) (v:Voter) (r_n:nat) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
    (
      (
        get_voter_opaque_round (get_state_up_to t3) v r_n = Some r
      )
      /\
      (
        length (Sets.to_list s) 
        >= 
        1+ Votes.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      ) 
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\ 
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters r_n))
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
    + Search ({?n = ?m}+{?n < ?m}+{?m < ?n }).
      (*TODO in 3.8 *)
Admitted.


Theorem theorem_4_1 `{Io} 
  {n1 n2 :nat} 
  (b1:Block n1) 
  (b2:Block n2) 
  (round_finalized_1 round_finalized_2:nat)
  (t1 t2:nat)
  (un_related:Unrelated b1 b2)
  (state:State)
  (t:Time)
  (state_is_from_protocol: state =  get_state_up_to t)
  (b1_in:List.In (to_any b1,t1, round_finalized_1) (global_finalized_blocks state))
  (b2_in:List.In (to_any b2,t2, round_finalized_2) (global_finalized_blocks state))
  (symmetry_hipotesis:round_finalized_1 <= round_finalized_2)
  : exists (t3:Time) (v:Voter) (r_n:nat) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
    (
      (
        get_voter_opaque_round (get_state_up_to t3) v r_n = Some r
      )
      /\
      (
        length (Sets.to_list s) 
        >= 
        1+ Votes.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      ) 
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\ 
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters r_n))
    ).
Proof.
  pose (Arith.Compare_dec.lt_eq_lt_dec round_finalized_1 round_finalized_2 ) as trico.
  destruct trico as [[trico4 | trico2]| trico3].
  - apply (theorem_4_1_lt b1 b2 round_finalized_1 round_finalized_2 t1 t2 un_related state t state_is_from_protocol b1_in b2_in);try assumption.  
  - rewrite state_is_from_protocol in b1_in.
    rewrite state_is_from_protocol in b2_in.
    rewrite <- trico2 in b2_in.
    destruct (theorem_4_1_eq b1 b2 round_finalized_1 t1 t2 un_related  t b1_in b2_in) as [t3 [v3 [r [s remain]]]].
    exists t3.
    exists v3.
    exists round_finalized_1. 
    exists r.
    exists s.
    assumption.
  - pose (Blocks.unrelated_symmetric b1 b2 un_related) as un_related2.
    apply (theorem_4_1_lt b2 b1 round_finalized_2 round_finalized_1 t2 t1 un_related2 state t state_is_from_protocol b2_in b1_in);try assumption.  
Qed.

Definition voter_is_hones_at_round `{Io} (v:Voter) (r:nat) : bool
  := 
  0<? ListFacts.count Nat.eqb v (get_round_honest_voters r).


Corollary corollary_4_3 
  `{Io}
  (round_finalized_number:nat)
  (time_finalied:Time)
  (b_finalized:AnyBlock)
  (v:Voter)
  (r_n:nat)
  (is_honest: voter_is_hones_at_round v r_n = true)
  (t_increment:Time)
  (r_n_geq: r_n >= round_finalized_number)
  (opaque_r_n : OpaqueRound.OpaqueRoundState)
  (opaque_from_state
    : 
    get_voter_opaque_round (get_state_up_to (t_increment + time_finalied)%nat ) v r_n 
    = Some opaque_r_n
  )
  (r_n_completable:
   OpaqueRound.is_completable opaque_r_n = true
  )
  :exists (eb:AnyBlock),
    (
      OpaqueRound.get_estimate opaque_r_n
      = 
      Some eb 
    )
    /\ 
    (
      Blocks.is_prefix (projT2 b_finalized) (projT2 eb) = true
    ).
Proof.
  (*TODO: delayed until 3.8
   *)
  Admitted.





Close Scope type_scope.
