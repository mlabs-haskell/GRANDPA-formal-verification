Require Import Blocks.                 
Require Import Votes.                  
Require Import Preliminars.
Require List.
Require Import Functors.

Require Import Nat.
Require Arith.Compare_dec.
Require Import Program.Equality.

Definition Time := nat.

Inductive RoundState 
      {preview_number precommit_number last_block_number}
  (preview_voters:Voters preview_number) 
  (precommit_voters: Voters precommit_number)
  (round_start_time:Time) 
  (last_block: Block last_block_number)
  (round_number: nat)
  : Time ->  Type :=
  | InitialRoundState 
    : RoundState preview_voters precommit_voters round_start_time last_block round_number 0
  | RoundStateUpdate 
    {old_time_increment: Time}
    (old_state: RoundState 
      preview_voters precommit_voters 
      round_start_time last_block round_number old_time_increment)
    (time_increment: Time)
    (new_preview_votes: Votes preview_voters last_block)
    (new_precommit_votes: Votes precommit_voters last_block)
    : RoundState preview_voters precommit_voters round_start_time last_block 
      round_number
      (time_increment+ old_time_increment).

Section State1.

Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment: nat}.




Definition get_preview_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes preview_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ _ _ new_preview_votes _ => new_preview_votes
  end.

Definition get_precommit_votes
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes precommit_voters last_block)
  :=
  match round_state with
  | InitialRoundState _ _ _ _ _=> VotesC _ _ List.nil (* No votes in initial round state *)
  | RoundStateUpdate _ _ _ _ _ _ _ _ new_precommit_votes => new_precommit_votes
  end.

End State1.


Fixpoint get_all_preview_votes{preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes preview_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ _ => VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ old_state  _ new_preview_votes _ => mergeVotes (get_all_preview_votes old_state) new_preview_votes
  end.

Fixpoint get_all_precommit_votes{preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  (Votes precommit_voters last_block)
  := 
  match round_state with
  | InitialRoundState _ _ _ _ _=> VotesC _ _ List.nil 
  | RoundStateUpdate _ _ _ _ _ old_state  _ _ new_precommit_votes => mergeVotes (get_all_precommit_votes old_state) new_precommit_votes
  end.

Definition voter_voted_in_preview {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (voter:Voter)
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  bool
  := 
  let preview_votes := get_all_preview_votes round_state
  in
    if in_Voters_bool voter preview_voters 
    then voter_voted_in_votes voter preview_votes
    else true.

Definition  voter_voted_in_precommit {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (voter:Voter)
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : 
  bool
  := 
  let precommit_votes := get_all_precommit_votes round_state
  in
    if in_Voters_bool voter precommit_voters 
    then voter_voted_in_votes voter precommit_votes
    else true.



Variant Estimate {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  {time_increment: Time}
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : {n & Block n} -> Type
  :=
    | EstimateOrigin : round_number = 0 -> Estimate round_state (existT _ 0 OriginBlock)
    |EstimateC 
    {new_block_number : nat}
    (new_block : Block new_block_number)
    (is_children: IsChildren new_block last_block)
    {g_block_number: nat}
    (g_preview: Block g_block_number)
    (g_preview_is_some : g ( get_preview_votes round_state) = Some (existT _ g_block_number g_preview))
    (new_block_is_ancestor_of_g: Prefix new_block g_preview)
    : Estimate round_state (existT _ new_block_number new_block).



Section State2.

Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment : Time}.


(* Projection of the type Estimate *)
Definition get_estimate_block
  {round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment}
  {n}
  {block : Block n}
  (estimate :Estimate round_state (existT _ n block))
  : Block n
  :=
  match estimate with
    | EstimateOrigin _ _ => OriginBlock
    | EstimateC _ new_block _ _ _ _ => new_block
  end.

Fixpoint get_estimate_aux_recursive {gv_block_number block_number:nat} 
  (block:Block block_number)
  (gv:Block gv_block_number)
  (precommit_supermajority_blocks: list (AnyBlock*nat))
  : option AnyBlock
  :=
    if block_number <? gv_block_number
    then 
      let find_block any_block := 
        match any_block with
          | (existT _ block_number block,_)
            => Blocks.eqb gv block
        end
      in
      match List.find find_block precommit_supermajority_blocks with 
        | None 
            => match gv with
                | OriginBlock => None
                | NewBlock old_block _ 
                    =>  
                    get_estimate_aux_recursive 
                      block
                      old_block 
                      precommit_supermajority_blocks
                end
        | Some (any_block,_)
            => Some any_block
      end
    else None.

Definition get_estimate_aux 
  (preview_votes: Votes preview_voters last_block) 
  (precommit_votes: Votes precommit_voters last_block)
  : option AnyBlock
  :=
  match g preview_votes with 
  | None => None
  | Some g_preview_votes =>
    let precommit_supermajority_blocks := 
      get_supermajority_blocks precommit_votes
    in
      get_estimate_aux_recursive 
        last_block
        (projT2 g_preview_votes) 
        precommit_supermajority_blocks
  end.

Definition get_estimate 
  (round_state: 
    RoundState preview_voters precommit_voters  
      round_time last_block round_number 
      time_increment
  )
  : option AnyBlock
  :=
 match round_state  with
  | InitialRoundState _ _ _ _ _ => 
      if Nat.eqb round_number 0 then
      Some (existT _ 0 OriginBlock)
      else
      None
  | RoundStateUpdate _ _ _ _ _ _ _ _ _=> 
    let all_preview_votes := get_all_preview_votes round_state
    in
    let all_precommit_votes := get_all_precommit_votes round_state
    in
    get_estimate_aux all_preview_votes all_precommit_votes
  end.


End State2.

Section State3.
Context {preview_number precommit_number last_block_number : nat}.
Context {preview_voters:Voters preview_number }.
Context {precommit_voters: Voters precommit_number}.
Context {last_block: Block last_block_number}.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment : Time}.


Lemma get_estimate_aux_recursive_is_none_on_nil : 
  forall {m} (last_block_lemma:Block m) 
         {n} (block:Block n) ,   
                    get_estimate_aux_recursive 
                      last_block
                      block
                      nil = None.
Proof.
  intros m last_block_lemma. 
  - intro n. induction n as [|n HInductive]
    ;intro block. 
    + dependent inversion block.
      simpl. reflexivity.
    + dependent inversion block. 
      simpl. 
      destruct (last_block_number <? S n).
      ++  apply HInductive.
      ++  reflexivity.
Qed.
      


Lemma get_estimate_result_is_children  
  {block_number:nat}
  {block:Block block_number}
  (round_state: 
    RoundState preview_voters precommit_voters  
      round_time last_block round_number 
      time_increment
  )
  (round_is_not_zero: round_number <> 0)
  (get_estimate_result
    : get_estimate round_state = Some (existT _ block_number block)
  )
  : Prefix block last_block.
Proof.
  unfold get_estimate in get_estimate_result.
  destruct round_state eqn:H_state.
  - destruct round_number eqn:H_round_number.
    + contradiction.
    + simpl in get_estimate_result.
      discriminate get_estimate_result.
  - simpl in get_estimate_result.
    unfold get_estimate_aux in get_estimate_result.
    destruct (g (mergeVotes (get_all_preview_votes r) new_preview_votes)) 
      as [g_preview|] eqn:g_preview_eq.
    2: 
      discriminate get_estimate_result.
    + destruct 
        (get_supermajority_blocks
          (mergeVotes (get_all_precommit_votes r) new_precommit_votes)
        ) eqn:precommit_supermajority_blocks_eq.
      ++ assert (get_estimate_aux_recursive last_block (projT2 g_preview) nil = None) as is_nil.
         {
            apply (get_estimate_aux_recursive_is_none_on_nil last_block (projT2 g_preview) ).
          }
         rewrite is_nil in get_estimate_result.
         discriminate.
      ++ unfold get_estimate_aux_recursive in get_estimate_result.
         simpl in get_estimate_result.
         Admitted.
(* TODO: Finish it *)


Theorem get_estimate_output_is_estimate 
  {block_number:nat}
  {block:Block block_number}
  (round_state: 
    RoundState preview_voters precommit_voters  
      round_time last_block round_number 
      time_increment
  )
  (get_estimate_result
    : get_estimate round_state = Some (existT _ block_number block)
  )
  : Estimate round_state (existT _ block_number block).
Proof.
Admitted.
(*  
dependent destruction block.
  - refine (EstimateOrigin round_state _).
*)



Variant Completable 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : Type
  :=
  | CompletableBelowPreview {number_and_block}
      (e: Estimate  round_state number_and_block)
      {g_block_number: nat}
      (g_preview: Block g_block_number)
      (g_preview_is_some 
        : g ( get_preview_votes round_state) 
          = Some (existT _ g_block_number g_preview)
      )
      (new_block_is_below_g: projT1 number_and_block < g_block_number)
  | CompletableByImpossible 
      {g_block_number: nat}
      (g_preview: Block g_block_number)
      (
        g_preview_is_some 
        : g ( get_preview_votes round_state) 
          = Some (existT _ g_block_number g_preview)
      )
      (cant_have_supermajority 
        : forall n (block : Block n) 
          , g_block_number < n 
          -> has_supermajority (get_precommit_votes round_state) 
            = false
      )
  .

Definition try_to_complete_round
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : option (Completable round_state).
(* needs to define possible and impossible supermajority*)
Admitted.

Definition is_completable 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number time_increment)
  : bool
  :=
  match try_to_complete_round round_state with
  | None => false
  | _ => true
  end.



End State3.

Require Import Message.

Variant VoterCategory  :=
  | Bizantine
  | Honest.

Variant VoterVoteRight := 
  | VotePrecommit
  | VotePrevote
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

Lemma aux_nat_to_fin (n:nat) (upper_bound:nat) 
  : option (Vectors.Fin.t upper_bound).
Proof.
  destruct (Vectors.Fin.of_nat n upper_bound).
  - refine (Some t).
  - refine None.
Qed.


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
  let maybe_index 
    : option (Vectors.Fin.t vs.(voter_last_round_know) ) 
    := aux_nat_to_fin 
    msg.(Message.round) vs.(voter_last_round_know)
  in 
  let maybe_round 
      : option OpaqueRoundState 
      :=  (map (Vectors.VectorDef.nth vs.(voter_rounds)) maybe_index)
  in
  let maybe_updated 
      : option OpaqueRoundState
      :=
    map (fun f => f msg ) (map
        update_opaqueRound_with_precommit_message 
        maybe_round)
  in
  let maybe_update_function 
    : option (OpaqueRoundState -> VectorDef.t OpaqueRoundState (voter_last_round_know vs))
      := map (f:=option) (Vectors.VectorDef.replace vs.(voter_rounds)) maybe_index
  in
  match maybe_update_function  with
  | Some f =>
    match maybe_updated with
    |Some updated => 
        let new_tower := f updated
        in
        {|
        voter_round_number := vs.(voter_round_number)
        ;prevoted_block := vs.(prevoted_block)
        ;precommited_block := vs.(precommited_block)
        ;last_brodcasted_block := vs.(last_brodcasted_block)
        ;voter_last_round_know:= vs.(voter_last_round_know)
        ;voter_rounds := new_tower 
        |}
    | _ => vs
    end
  | _ => vs
  end.

Definition update_voter_state_with_preview  (msg:Message) (vs: VoterState) 
  : VoterState
  :=
  let maybe_index 
    : option (Vectors.Fin.t vs.(voter_last_round_know) ) 
    := aux_nat_to_fin 
    msg.(Message.round) vs.(voter_last_round_know)
  in 
  let maybe_round 
      : option OpaqueRoundState 
      :=  (map (Vectors.VectorDef.nth vs.(voter_rounds)) maybe_index)
  in
  let maybe_updated 
      : option OpaqueRoundState
      :=
    map (fun f => f msg ) (map
        update_opaqueRound_with_preview_message 
        maybe_round)
  in
  let maybe_update_function 
    : option (OpaqueRoundState -> VectorDef.t OpaqueRoundState (voter_last_round_know vs))
      := map (f:=option) (Vectors.VectorDef.replace vs.(voter_rounds)) maybe_index
  in
  match maybe_update_function  with
  | Some f =>
    match maybe_updated with
    |Some updated => 
        let new_tower := f updated
        in
        {|
        voter_round_number := vs.(voter_round_number)
        ;prevoted_block := vs.(prevoted_block)
        ;precommited_block := vs.(precommited_block)
        ;last_brodcasted_block := vs.(last_brodcasted_block)
        ;voter_last_round_know:= vs.(voter_last_round_know)
        ;voter_rounds := new_tower 
        |}
    | _ => vs
    end
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
        if Nat.leb t (msg.(Message.time)+ global_time_constant)
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


Definition voter_round_step `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match Dictionary.lookup Nat.eqb voter state.(voters_state)with
  | Some voter_state_ => state 
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
