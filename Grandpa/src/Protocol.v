Require Import Blocks.                 
Require Import Votes.                  
Require Import Preliminars.
Require Import Round.
Require Import Estimate.

Require Import Message.

Require Import Functors.
Require Import Vectors.

Require Import Nat.
Require Import Program.Equality.
(*Require Arith.Compare_dec.
 *)


Variant VoterCategory  :=
  | Bizantine
  | Honest.

Variant VoterVoteRight := 
  | VotePrevote
  | VotePrecommit
  | VoteBoth.

Variant VoterKind : Type := 
  | VoterVoteKindC (category:VoterCategory) (right: VoterVoteRight).

Class Io := {
  global_time_constant: nat;
  block_producer {n} (last_block:Block n) : 
    list {b:AnyBlock & Prefix last_block (projT2 b)};
  io_accept_vote : Time -> Message -> Voter -> bool;
  (* the nat is the round number*)
  io_get_round_voters:  nat -> Dictionary.Dictionary nat VoterKind;
  io_get_round_primary : nat -> Voter;
  block_producer_not_emtpy{n} {last_block:Block n} 
  : block_producer(last_block) <> nil;
  primary_consistent 
    : forall r , 
        List.In 
        (io_get_round_primary r) 
        (List.map fst (Dictionary.to_list (io_get_round_voters r )));
}.

Variant OpaqueRoundState: Type := 
  | OpaqueRoundStateC {preview_number precommit_number last_block_number round_number}
    {preview_voters:Voters preview_number}
    {precommit_voters: Voters precommit_number}
    {round_start_time:Time}
    {last_block: Block last_block_number}
    {time:Time}
    (round_state: 
      RoundState 
        preview_voters precommit_voters round_start_time last_block round_number time 
    ).

Definition Vec := Vector.t.

Definition RoundTower  
  := Vec OpaqueRoundState .

(**
A voter has 3 states:
  - Waiting to emit prevote (called preview in code) [prevoted_block = None] [precommited_block=None]
   - Waiting to emit precommit  [precommited_block = None]
   - Waiting to start a new round [prevoted_block] and [precommited_block] can be anything
We use the VoterKind to know the state.

Additionally the primary has to handle the broadcast of a 
finalized block, but this is done separately in the simulation
**)

Record VoterState := {
  voter_round_number : nat 
  ;prevoted_block : option AnyBlock
  ;precommited_block : option AnyBlock
  (** We only store the last block received from a primary and we only keep the highest and latest (in that order)**)
  ;last_brodcasted_block : AnyBlock 
  ;voter_last_round_know: nat
  ;voter_rounds : RoundTower voter_last_round_know
  }.

Definition update_voter_state_with_last_block  (vs:VoterState) (block: AnyBlock)
  : VoterState
  := 
    let (old_level,_) := vs.(last_brodcasted_block)
    in
  let (block_level,_) := block
    in
    if old_level <? block_level then  
      {|
        voter_round_number := vs.(voter_round_number)
        ;prevoted_block := vs.(prevoted_block)
        ;precommited_block := vs.(precommited_block)
        ;last_brodcasted_block := block
        ;voter_last_round_know:= vs.(voter_last_round_know)
        ;voter_rounds := vs.(voter_rounds)
        |}
    else
      vs.


(*TODO: merge precommit and preview logic in a single function *)
Definition update_round_with_precommit_message 
  {preview_number precommit_number last_block_number round_number :nat}
  {preview_voters:Voters preview_number }
  {precommit_voters: Voters precommit_number}
  {last_block: Block last_block_number}
  {round_start_time : Time}
  {time_increment:Time}
  (r:RoundState preview_voters precommit_voters round_start_time last_block round_number time_increment) 
  (msg:Message)
  : OpaqueRoundState
  :=
  match Message.message_to_precommit_vote msg precommit_voters last_block with
  | Some new_votes => 
      let new_time_increment := msg.(Message.time) - (round_start_time + time_increment)
      in
        OpaqueRoundStateC (
          RoundStateUpdate 
            preview_voters 
            precommit_voters 
            round_start_time 
            last_block 
            round_number 
            r 
            new_time_increment 
            (VotesC preview_voters last_block List.nil) 
            (VotesC precommit_voters last_block (List.cons new_votes List.nil))
          )
  | _ => OpaqueRoundStateC r
  end.

Definition update_round_with_preview_message 
  {preview_number precommit_number last_block_number round_number :nat}
  {preview_voters:Voters preview_number }
  {precommit_voters: Voters precommit_number}
  {last_block: Block last_block_number}
  {round_start_time : Time}
  {time_increment:Time}
  (r:RoundState preview_voters precommit_voters round_start_time last_block round_number time_increment) 
  (msg:Message)
  : OpaqueRoundState
  :=
  match Message.message_to_preview_vote msg preview_voters last_block with
  | Some new_votes => 
      let new_time_increment := msg.(Message.time) - (round_start_time + time_increment)
      in
        OpaqueRoundStateC (
          RoundStateUpdate 
            preview_voters 
            precommit_voters 
            round_start_time 
            last_block 
            round_number 
            r 
            new_time_increment 
            (VotesC preview_voters last_block (List.cons new_votes List.nil))
            (VotesC precommit_voters last_block List.nil) 
          )
  | _ => OpaqueRoundStateC r
  end.


Definition update_opaqueRound_with_precommit_message
  (opaque:OpaqueRoundState)
  (msg:Message)
  : OpaqueRoundState
  :=
  match opaque with
  | OpaqueRoundStateC r => update_round_with_precommit_message r msg
  end.

Definition update_opaqueRound_with_preview_message
  (opaque:OpaqueRoundState)
  (msg:Message)
  : OpaqueRoundState
  :=
  match opaque with
  | OpaqueRoundStateC r => update_round_with_preview_message r msg
  end.


Definition update_voter_state_with_precommit  (msg:Message) (vs: VoterState) 
  : VoterState
  :=
  let maybe_round :option OpaqueRoundState := Vectors.get vs.(voter_rounds) msg.(round) 
  in
  let maybe_updated 
      : option OpaqueRoundState
      :=
    map (fun f => f msg ) (map
        update_opaqueRound_with_precommit_message 
        maybe_round)
  in
  let maybe_tower 
    := 
    map (Vectors.update vs.(voter_rounds) msg.(round)) maybe_updated
  in
  match maybe_tower with
  | Some new_tower =>
        {|
        voter_round_number := vs.(voter_round_number)
        ;prevoted_block := vs.(prevoted_block)
        ;precommited_block := vs.(precommited_block)
        ;last_brodcasted_block := vs.(last_brodcasted_block)
        ;voter_last_round_know:= vs.(voter_last_round_know)
        ;voter_rounds := new_tower 
        |}
  | _ => vs
  end.

Definition update_voter_state_with_preview  (msg:Message) (vs: VoterState) 
  : VoterState
  :=
  let maybe_round :option OpaqueRoundState := Vectors.get vs.(voter_rounds) msg.(round) 
  in
  let maybe_updated 
      : option OpaqueRoundState
      :=
    map (fun f => f msg ) (map
        update_opaqueRound_with_preview_message 
        maybe_round)
  in
  let maybe_tower 
    := 
    map (Vectors.update vs.(voter_rounds) msg.(round)) maybe_updated
  in
  match maybe_tower with
  | Some new_tower =>
        {|
        voter_round_number := vs.(voter_round_number)
        ;prevoted_block := vs.(prevoted_block)
        ;precommited_block := vs.(precommited_block)
        ;last_brodcasted_block := vs.(last_brodcasted_block)
        ;voter_last_round_know:= vs.(voter_last_round_know)
        ;voter_rounds := new_tower 
        |}
  | _ => vs
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
      match msg.(Message.kind) with 
      | PreCommitMessage 
          => update_voter_state 
              state 
              voter 
              (update_voter_state_with_precommit msg voter_state_)
      | PreViewMessage 
          => 
          update_voter_state 
          state 
          voter 
          (update_voter_state_with_preview msg voter_state_)
      | EstimateMessage 
          => 
          update_voter_state 
          state 
          voter 
          (update_voter_state_with_last_block voter_state_ msg.(Message.block))
      | FinalizationMessage 
          =>
          update_voter_state 
          state 
          voter 
          (update_voter_state_with_last_block voter_state_ msg.(Message.block))
      end
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

Definition prevoter_step `{Io} 
  (t:Time) 
  (state:State) 
  (voter:Voter) 
  (category:VoterCategory)
  (vs:VoterState)
  : State
  :=
  let tower := vs.(voter_rounds)
  in
  let maybe_index := aux_nat_to_fin vs.(voter_round_number) vs.(voter_last_round_know)
  in
  state.
  (* 
  match try_to_complete_round round  with
  | Some(completable) => state
  | None=> state
  end.
   *)


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
      match Dictionary.lookup Nat.eqb voter (io_get_round_voters voter_state_.(voter_round_number)) with
      | Some(VoterVoteKindC category kind_) => 
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
