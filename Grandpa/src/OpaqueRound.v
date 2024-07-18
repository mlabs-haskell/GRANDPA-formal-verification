Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import Voters.
Require Import Round.
Require Import Estimate.

Require Import Message.

Variant OpaqueRoundState: Type := 
  | OpaqueRoundStateC {total_voters round_number}
    {prevote_voters:Voters}
    {precommit_voters: Voters}
    {round_start_time:Time}
    {time:Time}
    (round_state: 
      RoundState 
        total_voters 
        prevote_voters 
        precommit_voters 
        round_start_time 
        round_number 
        time 
    ).

Definition get_prevote_voters (o:OpaqueRoundState) : Voters
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_prevote_voters r 
  end.

Definition get_precommit_voters (o:OpaqueRoundState) : Voters
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_precommit_voters r 
  end.

Definition get_start_time (o:OpaqueRoundState) : Time
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_start_time r 
  end.

Definition get_round_number (o:OpaqueRoundState) : nat
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_round_number r 
  end.

Definition get_total_voters (o:OpaqueRoundState) : nat
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_total_voters r 
  end.

Definition get_all_prevote_votes (o:OpaqueRoundState) : (Votes (get_prevote_voters o))
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_prevote_votes r 
  end.

Definition get_all_precommit_votes (o:OpaqueRoundState) : (Votes (get_precommit_voters o))
  :=
  match o with 
  | OpaqueRoundStateC r => Round.get_precommit_votes r 
  end.

Definition is_completable (o:OpaqueRoundState) 
  : bool
  :=
  match o with 
  | OpaqueRoundStateC r => Estimate.is_completable r 
  end.

Definition get_estimate (o:OpaqueRoundState) 
  : option AnyBlock
  :=
  match o with 
  | OpaqueRoundStateC r => Estimate.get_estimate r 
  end.


Definition update_votes_with_msg
  (opaque:OpaqueRoundState)
  (msg:Message)
  : OpaqueRoundState
  :=
  match opaque with
  | OpaqueRoundStateC r =>
    let bizantiners_number := Round.get_total_voters r
    in
    let prevote_voters := Round.get_prevote_voters r
    in
    let precommit_voters := Round.get_precommit_voters r
    in
    let start_time := Round.get_start_time r
    in
    let old_increment := Round.get_start_time r
    in
    let round_number := Round.get_round_number r
    in
    let new_time_increment := msg.(Message.time) - (start_time + old_increment)
    in
    match Message.message_to_prevote_vote msg prevote_voters with
    | Some new_votes => 
       OpaqueRoundStateC (
         RoundStateUpdate 
           bizantiners_number
           prevote_voters 
           precommit_voters 
           start_time 
           round_number 
           r 
           new_time_increment 
           (VotesC prevote_voters (List.cons new_votes List.nil))
           (VotesC precommit_voters List.nil) 
         )
    | _ => 
      match Message.message_to_precommit_vote msg precommit_voters with
      | Some new_votes => 
         OpaqueRoundStateC (
           RoundStateUpdate 
             bizantiners_number
             prevote_voters 
             precommit_voters 
             start_time 
             round_number 
             r 
             new_time_increment 
             (VotesC prevote_voters List.nil) 
             (VotesC precommit_voters (List.cons new_votes List.nil))
           )
      | _ => opaque
      end
     end
  end.

