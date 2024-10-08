Require Import Blocks.AnyBlock.
Require Import Voters.
Require Import Preliminars.
Require Estimate.
Require OpaqueRound.
Require Round.
Require Import Time.
Require Import RoundNumber.
Require Import VoterState.
Require Import Vectors.
Require Import Sets.
Require Import Message.
Require Import DataTypes.List.Count.
Require Import DataTypes.Option.
Require Import Protocol.State.
Require Import Protocol.StateMessages.
Require Import Protocol.FinalizedBlock.

Require Import Program.Equality.
Require Import PeanoNat.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Require Import Protocol.Io.

(*Require Arith.Compare_dec.
 *)

Require Import Lia.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

(** *Protocol

The main functions of this module are:
  - [get_state_up_to]
  - [voters_round_step]

Of the same importance but no defined in this module is the
  [StateMessages.update_votes] function.

The [get_state_up_to] function is in charge of performing the
main loop of the simulation. It just take the 0 state
and feed the [voter_round_step] and  [StateMessages.update_votes] functions
with the right states for the corresponding [Time] until
we reach the desired Time.

At every time [t], we have two stages:
  - Update the local state of every voter according to the messages received
    by that voter up to this time.
  - Proceed to run the Grandpa protocol or to act as a byzantine voter
    for every voter of the protocol.

The [StateMessages.update_votes] function models the message passing
between participants.

The [voters_round_step] function models the actions of the participants
at a particular time and global state of the protocol.

See the documentation of each function for details.

Other functions of high interest:

  - [prevoter_step_legit] what a honest prevoter does
  - [precommit_step_legit] what a honest precommiter does
  - [finalize_block]
*)


(**
Given a block [b], looks in all the blocks produced by block producer
for this round and time.
Filters all the blocks [x] such that [b <=? x].
And gets the block with the higher block number.
*)
Definition look_for_best_chain_for_block `{Io} (t:Time) (v:Voter) (ablock:AnyBlock)
  : option AnyBlock
  :=
  let (block_number,block) := ablock
  in
  let available_blocks := block_producer t v
  in
  let blocks_that_contains_it :=
    List.filter
    (fun x => AnyBlock.is_prefix ablock  x)
    (Sets.to_list available_blocks)
  in
  match blocks_that_contains_it with
  | List.nil => None
  | _ =>
    Some(
      List.fold_left
        (fun x y => if (x.(AnyBlock.block_number) <? y.(AnyBlock.block_number))%nat then y else x)
        blocks_that_contains_it
        (AnyBlock.to_any OriginBlock)
    )
  end.

(**
Creates a prevote message for the given block,
adds it to the local state (to set that the voter already voted),
and sends the message.
*)
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
          id:= Message.from_nat (1 + state.(message_count))
          ;Message.block:=b
          ;kind:=Message.PreVoteMessage
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
        |}
      in
        let
          up_prevote := VoterState.update_prevoted vs (Some b)
        in
        let up_round := VoterState.update_votes_with_msg up_prevote new_message
        in
        advance_count
          (update_voter_state (update_message state new_message) voter up_round).

(**
Creates a precommit message for the given block,
adds it to the local state (to set that the voter already voted),
and sends the message.
*)
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
          id:= Message.from_nat (S state.(message_count))
          ;Message.block:=b
          ;kind:=Message.PreCommitMessage
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
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
          id:= Message.from_nat (S state.(message_count))
          ;Message.block:=b
          ;kind:=Message.EstimateMessage
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
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


(**
Create a message that the given block is being finalized,
adds it to both the local collection of finalized blocks,
and the global collection.
Then we send the message.
*)
Definition build_and_send_finalized_block
  (t:Time)
  (state:State)
  (voter:Voter)
  (vs:VoterState)
  (b:AnyBlock)
  (votes:Message.FinalizeBlock)
  (opaque:OpaqueRound.OpaqueRoundState)
  :State
  :=
      let new_message : Message.Message
        :=
        {|
          id:= Message.from_nat (S state.(message_count))
          ;Message.block:=b
          ;kind:=Message.FinalizationMessage votes
          ;round:=vs.(VoterState.round_number)
          ;Message.time:=t
          ;voter:=voter
          ;processed_by:=Sets.from_list (voter::List.nil)
        |}
      in
      let updated_voter_state
        :=
        VoterState.update_add_finalized_block vs b
      in
      let finalized_block :=
        FinalizedBlock.make_with_round t voter b opaque
      in
      State.update_add_finalized_block
        (
        advance_count
          (update_voter_state
            (update_message state new_message)
            voter updated_voter_state
          )
        )
        finalized_block.


Definition prevoter_step_aux `{Io} (t:Time) (state:State) (voter:Voter) (vs:VoterState)
  :State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)-1) with
  |Some (OpaqueRound.OpaqueRoundStateC previous_round)
    =>
    let ref_block :=
      match vs.(last_brodcasted_block) with
      | Some b =>
          match
            (g (Round.get_all_prevote_votes previous_round)
              ,Estimate.get_estimate previous_round
            )
          with
          | (Some g_prev, Some estimate_prev)
              =>
              if
                Block.is_prefix estimate_prev.(AnyBlock.block) b.(AnyBlock.block)
                && Block.is_prefix b.(AnyBlock.block) g_prev.(AnyBlock.block)
              then Some b
              else Estimate.get_estimate previous_round
          | _ => Estimate.get_estimate previous_round
          end
      | None => Estimate.get_estimate previous_round
      end
    in
    match map (look_for_best_chain_for_block t voter) ref_block with
    | Some (Some b) => build_and_send_prevote t state voter vs b
    | _ => state
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
    match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)) with
    | Some (OpaqueRound.OpaqueRoundStateC round_) =>
      match Estimate.try_to_complete_round round_  with
      | Some _ =>
          prevoter_step_aux t state voter vs
      | None=>
          if t<=? Round.get_start_time round_ + (Time.from_nat 2)*global_time_constant
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
    match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)) with
    | Some (OpaqueRound.OpaqueRoundStateC r) =>
      match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number) - 1) with
      | Some (OpaqueRound.OpaqueRoundStateC r_prev) =>
        match (g (Round.get_all_prevote_votes r), Estimate.get_estimate r_prev) with
        | (Some g_r,Some estimate_prev)
          =>
          (* TODO: add third condition of precommit *)
          if (t <? Round.get_start_time r + (Time.from_nat 4)*global_time_constant)
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
    (fun acc y => max acc y.(AnyBlock.block_number))
    (Sets.to_list finalized_blocks)
    0.

(**
A block $b = g (C_{r,v})$ can be finalized by a voter [v] if :
  - [b] its block number is above the all the finalized blocks the voter knows.
  - [b] has a supermajority in $V_{r,v}$
*)
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
            (b.(AnyBlock.block_number) <? max_block_number)%nat
          )
          finalized_blocks
        ) && Votes.block_has_supermajority b (Round.get_all_prevote_votes r)
      then
        Some b
      else None
    end
  end.

Definition get_voter_kind_for_round `{Io} (v:Voter) (round_number:RoundNumber)
  :option VoterKind
  :=
  Dictionary.lookup  v (io_get_round_voters round_number).

Definition get_voter_state (v:Voter) (state:State)
  :option VoterState
  :=
  Dictionary.lookup  v state.(voters_state) .

Definition is_voter_for_round `{Io} (v:Voter) (round_number:RoundNumber)
  : bool
  :=
  is_some (get_voter_kind_for_round v round_number).

(**
All the blocks on all the rounds that a voter can finalize that haven
been finalized.

First, we get all the blocks that the current voter knows has been finalized.
Then get all the rounds in witch the current voter has participated
until now.
We inspect every round to see if we can finalize now a block that haven been
finalized before.
*)
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
            (RoundNumber.to_nat vs.(VoterState.round_number)-1)
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
  transitivity (RoundNumber.to_nat (VoterState.round_number vs)).
  rewrite PeanoNat.Nat.sub_1_r.
  apply PeanoNat.Nat.le_pred_l.
  apply PeanoNat.Nat.le_succ_diag_r.
Qed.

(**
Made to be used together with get_blocks_to_finalize.
Take a block and all the info needed to build a [FinalizeBlock],
then adds it to the finalized_blocks in the global state.
*)
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
    build_and_send_finalized_block t state voter vs b fin_msg opaque
  | None => state
  end.

(**
Multiple voters may finalize the same block if they notice it can be
finalized but haven't received a finalization message.
*)
Definition finalization `{Io} (t:Time) (state:State)
  (voter:Voter) (vs:VoterState)
  :State
  :=
  List.fold_left
    (finalize_block t voter)
    (get_blocks_to_finalize voter vs)
    state.


(**
See if the current round is completable and advance to next round in such case.
If voter is the primary voter, we also broadcast the estimate.
*)
Definition wait_step_for_new_round `{Io}
  (t:Time)
  (voter:Voter)
  (vs:VoterState)
  (state:State)
  : State
  :=
  let tower := vs.(VoterState.rounds)
  in
  match Vectors.get tower (RoundNumber.to_nat vs.(VoterState.round_number)) with
  |Some (OpaqueRound.OpaqueRoundStateC r)
    =>
    match Estimate.try_to_complete_round r with
    | Some _ =>
        let new_vs :=
          State.init_next_round_voter_state_from
            (io_get_round_voters
              (
                (RoundNumber.from_nat 1)
                +
                vs.(VoterState.round_number)
              )
            )
            t
            vs
        in
        let updated_state := update_voter_state state voter new_vs
        in
        if voter_is_primary_for_round voter vs.(VoterState.round_number)
        then
          match Estimate.get_estimate r with
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


(**
If the participant (voter) has one of
the following conditions ([should_wait_for_next_round]):
   - Is a byzantine voter wishing to advance round.
   - Is a voter that already fulfilled it's obligations for this round.
   - Isn't a voter for this round.
We see if the current round (for the voter) is completable and if it is,
we advance the voter local state to a new round. Otherwise do nothing.

Otherwise we get perform the corresponding action for the particular voter
in the protocol or the byzantine action.
*)
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

(**
First we attempt to finalize all the blocks that we see as finalized but
that aren't still finalized by some one.

Then we really perform the Grandpa protocol or the byzantiner actions for
this time.
*)
(*TODO:
If this function is called by the members of voters_round_step,
the lookup for the voter must be always a Some. This is guaranteed by
the facts in the Io class and the way we construct the states.
We may add a theorem stating this.
*)
Definition voter_round_step `{Io} (t:Time) (state:State) (voter:Voter): State :=
  match get_voter_state voter state with
  | Some vs =>
    voter_round_step_aux
      t
      (finalization t state voter vs)
      voter
  | None => state
  end.

(**
This function models the grandpa protocol together with byzantine voters.

If a particular participant is byzantine in a round, they send messages
as dictated by the functions in Io.

If a participant is honest in a round, it follows the grandpa protocol.

This function expect to be run after a votes update.
This means that all participants of the model have received all the
messages that they are supposed to receive at this time.

As we separate the process of reception of votes/messages from the emission
of them, we can update every voter local state independently.
This update for a single voter is done in [voter_round_step].
*)
Definition voters_round_step `{Io} (t:Time) (state:State): State :=
  let voters := List.map fst (Dictionary.to_list state.(voters_state))
  in
    List.fold_left (voter_round_step t) voters state .


Fixpoint get_state_up_to_nat_aux `{Io} (n:nat) (state_0:State)
  : State
  :=
  match n with
  | 0 => state_0
  | S m
    =>
    let old_state := get_state_up_to_nat_aux m state_0
    in
    voters_round_step
      (Time.from_nat n)
      (update_votes (Time.from_nat n) old_state)
  end.

Definition initial_state `{io:Io} :State :=
  let
    zero_round_dict := io_get_round_voters (RoundNumber.from_nat 0)
  in
  State.make_initial_state_from zero_round_dict.

Definition get_state_up_to `{Io} (t:Time) : State
  :=
  get_state_up_to_nat_aux (Time.to_nat t) initial_state.


(*
This takes some time to compute, but it eventually does.
We believe the reason is that no Io instance is provide and the
computation must be made abstract. As such, we end with a 300k
lines result instead of a simple State.
*)
(* Compute get_state_up_to (Time.from_nat 1).*)

Close Scope bool.
Close Scope list.
Close Scope eqb.
Close Scope math.
Close Scope natWrapper.

