Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import Voters.
Require Import Round.
Require Import OpaqueRound.
Require Import Message.
Require List.

Require Import Classes.Functor.
Require Import Vectors.

Require Import PeanoNat.

Variant VoterCategory  :=
  | Bizantine
  | Honest.

Variant VoterVoteRight := 
  | VotePrevote
  | VotePrecommit
  | VoteBoth.

Variant VoterKind : Type := 
  | VoterKindC (category:VoterCategory) (right: VoterVoteRight).


(**
A voter has 3 states:
  - Waiting to emit prevote  [prevoted_block = None] [precommited_block=None]
   - Waiting to emit precommit  [precommited_block = None]
   - Waiting to start a new round [prevoted_block] and [precommited_block] can be anything
We use the VoterKind to know the state.

Additionally the primary has to handle the broadcast of a 
finalized block, but this is done separately in the simulation

If a message for a future round arrives while we are in another round
we store it in pending_messages 

Later when we enter in the round, the first action of a voter 
should be to process the pending messages for the round
**)

Record VoterState := {
  round_number : nat 
  ;prevoted_block : option AnyBlock
  ;precommited_block : option AnyBlock
  (** We only store the last block received from a primary and we only keep the highest and latest (in that order)**)
  ;last_brodcasted_block : option AnyBlock 
  (**Has to have size [round_number +1] so at the beginning we 
  can get the round 0 **)
  ;rounds : Vec OpaqueRoundState (S round_number)
  (** The nat is the round number **)
  ;pending_messages : Dictionary.Dictionary nat (list Message)
  ;finalized_blocks : Sets.DictionarySet AnyBlock
  }.


Local Open Scope vector_scope.

Definition make_initial_voter_state 
  (prevote_voters:Voters ) 
  (precommit_voters: Voters )
  : VoterState
  :=
  let total_voters 
      := 
      length 
        (Sets.to_list 
          (Sets.from_list Nat.eqb 
            (Sets.to_list 
             (Voters.to_set prevote_voters) 
             ++ Sets.to_list (Voters.to_set precommit_voters
             ) 
            )
          )
        )
  in
  (*
  The estimate for the 0 round at the beginning is just the Origin block 
  always!
  *)
  let
    round_zero  :=
      InitialRoundState 
        0 
        {|
          Votes.get_voters_dictionary:= Sets.empty
          ;Votes.round_number_of_voters:=0
        |} 
        {|
          Votes.get_voters_dictionary:= Sets.empty
          ;Votes.round_number_of_voters:=0
        |} 
        0
        0
  in
  let 
    round_one 
    := 
    InitialRoundState  total_voters prevote_voters precommit_voters 1 1 
  in
  let
    tower :Vec (OpaqueRound.OpaqueRoundState) 2 :=
    Vector.cons _
      (OpaqueRound.OpaqueRoundStateC round_one) 
      _
      (Vector.cons 
        _
        (OpaqueRound.OpaqueRoundStateC round_zero) 
        _
        (Vector.nil _)
      )
  in
  
  {|
    round_number := 1
    ;prevoted_block := None
    ;precommited_block := None
    ;last_brodcasted_block := Some (Blocks.to_any OriginBlock)
    ;rounds := tower
    ;pending_messages := Dictionary.empty
    ;finalized_blocks 
      := 
      Sets.from_list 
        Blocks.anyblock_eqb 
        (Blocks.to_any OriginBlock :: List.nil )
   |}.


Definition update_last_block  (vs:VoterState) (block:AnyBlock)
  : VoterState
  := 
    let (block_level,_) := block
    in
    let new_block := 
      match vs.(last_brodcasted_block) with
      | Some old_block => 
        let (old_level,_) := old_block
        in
        if old_level <? block_level then
          block
        else 
          old_block
      | None => block
      end
    in
    {|
      round_number := vs.(round_number)
      ;prevoted_block := vs.(prevoted_block)
      ;precommited_block := vs.(precommited_block)
      ;last_brodcasted_block := Some new_block
      ;rounds := vs.(rounds)
      ;pending_messages := vs.(pending_messages)
      ;finalized_blocks:= vs.(finalized_blocks)
      |}.

(*TODO: use update_last_block*)
Definition update_add_finalized_block  (vs:VoterState) (block:AnyBlock)
  : VoterState
  := 
    let (block_level,_) := block
    in
    let new_block := 
      match vs.(last_brodcasted_block) with
      | Some old_block => 
        let (old_level,_) := old_block
        in
        if old_level <? block_level then
          block
        else 
          old_block
      | None => block
      end
    in
    {|
      round_number := vs.(round_number)
      ;prevoted_block := vs.(prevoted_block)
      ;precommited_block := vs.(precommited_block)
      ;last_brodcasted_block := Some new_block
      ;rounds := vs.(rounds)
      ;pending_messages := vs.(pending_messages)
      ;finalized_blocks
        :=
        Sets.add Blocks.anyblock_eqb block vs.(finalized_blocks)
      |}.

Definition update_prevoted  (vs:VoterState) (maybe_block: option AnyBlock)
  : VoterState
  := 
     {|
       round_number := vs.(round_number)
       ;prevoted_block := maybe_block 
       ;precommited_block := vs.(precommited_block)
       ;last_brodcasted_block := vs.(last_brodcasted_block)
       ;rounds := vs.(rounds)
       ;pending_messages := vs.(pending_messages)
       ;finalized_blocks:= vs.(finalized_blocks)
      |}.

Definition update_precommit  (vs:VoterState) (block: option AnyBlock)
  : VoterState
  := 
    {|
      round_number := vs.(round_number)
      ;prevoted_block := vs.(prevoted_block)
      ;precommited_block := block
      ;last_brodcasted_block := vs.(last_brodcasted_block)
      ;rounds := vs.(rounds)
      ;pending_messages := vs.(pending_messages)
       ;finalized_blocks:= vs.(finalized_blocks)
    |}.

Definition update_rounds  (vs:VoterState) {tower_number:nat} 
  (new_rounds: Vec OpaqueRoundState (S tower_number))
  : VoterState
  := 
    {|
      round_number := tower_number
      ;prevoted_block := vs.(prevoted_block)
      ;precommited_block := vs.(precommited_block)
      ;last_brodcasted_block := vs.(last_brodcasted_block)
      ;rounds := new_rounds
      ;pending_messages := vs.(pending_messages)
       ;finalized_blocks:= vs.(finalized_blocks)
    |}.

Definition delete_pending_msg (vs:VoterState) (msg:Message)
  :VoterState
  :=
    {|
      round_number := vs.(round_number)
      ;prevoted_block := vs.(prevoted_block)
      ;precommited_block := vs.(precommited_block)
      ;last_brodcasted_block := vs.(last_brodcasted_block)
      ;rounds := vs.(rounds)
      ;pending_messages := 
        Dictionary.delete Nat.eqb msg.(Message.id) vs.(pending_messages)
       ;finalized_blocks:= vs.(finalized_blocks)
    |}.


(**
  If message is for a round bigger than the current one
  state is unchanged.
**)
Definition update_votes_with_msg  (vs: VoterState) (msg:Message)
  : VoterState
  :=
  let maybe_round :option OpaqueRoundState 
      := Vectors.get vs.(rounds) msg.(round) 
  in
  let 
    maybe_updated 
    : option OpaqueRoundState
    :=
    map 
      (fun r => OpaqueRound.update_votes_with_msg r msg)
      maybe_round
  in
  let maybe_tower 
    := 
    map (Vectors.update vs.(rounds) msg.(round)) maybe_updated
  in
  match maybe_tower with
  | Some new_tower => update_rounds vs new_tower
  (* The message came from a round further away than 
    the current one for the voter 
  *)
  | None => vs
  end.


(**
  If message came from a bigger round than the current one 
   we store it in pending_messages instead of processing it.
**)
Definition update_with_msg (vs:VoterState) (msg:Message)
  : VoterState
  := 
  if   msg.(Message.round) <=? vs.(round_number)
  then
      let updated_state 
        := 
        match msg.(Message.kind) with 
          | PreCommitMessage 
              => update_votes_with_msg vs msg
          | PreVoteMessage 
              => update_votes_with_msg vs msg
          | EstimateMessage 
              => update_last_block vs msg.(Message.block)
          | FinalizationMessage _ 
              => update_add_finalized_block vs msg.(Message.block)
        end
      in
       delete_pending_msg updated_state msg
  else
    let update previous new := 
      match previous with
      | Some prev =>  prev ++ new
      | None => new
      end
    in
        {|
        round_number := vs.(round_number)
        ;prevoted_block := vs.(prevoted_block)
        ;precommited_block := vs.(precommited_block)
        ;last_brodcasted_block := vs.(last_brodcasted_block)
        ;rounds := vs.(rounds)
        ;pending_messages 
          := 
          Dictionary.update_with 
            Nat.eqb
            vs.(round_number) 
            (List.cons msg List.nil) 
            update  
            vs.(pending_messages)
       ;finalized_blocks:= vs.(finalized_blocks)
        |}.

