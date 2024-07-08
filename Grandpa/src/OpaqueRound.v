Require Import Blocks.                 
Require Import Votes.                  
Require Import Round.

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

Definition update_votes_with_msg
  (opaque:OpaqueRoundState)
  (msg:Message)
  : OpaqueRoundState
  :=
  match opaque with
  | OpaqueRoundStateC r =>
    let bizantiners_number := get_total_voters r
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
