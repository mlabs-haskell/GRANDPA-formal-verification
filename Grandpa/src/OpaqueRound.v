Require Import Blocks.                 
Require Import Votes.                  
Require Import Round.

Require Import Message.

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

Definition update_votes_with_msg
  (opaque:OpaqueRoundState)
  (msg:Message)
  : OpaqueRoundState
  :=
  match opaque with
  | OpaqueRoundStateC r =>
    let last_block := Round.get_last_block r
    in
    let preview_voters := Round.get_preview_voters r
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
    match Message.message_to_preview_vote msg preview_voters  last_block with
    | Some new_votes => 
       OpaqueRoundStateC (
         RoundStateUpdate 
           preview_voters 
           precommit_voters 
           start_time 
           last_block 
           round_number 
           r 
           new_time_increment 
           (VotesC preview_voters last_block (List.cons new_votes List.nil))
           (VotesC precommit_voters last_block List.nil) 
         )
    | _ => 
      match Message.message_to_precommit_vote msg precommit_voters  last_block with
      | Some new_votes => 
         OpaqueRoundStateC (
           RoundStateUpdate 
             preview_voters 
             precommit_voters 
             start_time 
             last_block 
             round_number 
             r 
             new_time_increment 
             (VotesC preview_voters last_block List.nil) 
             (VotesC precommit_voters last_block (List.cons new_votes List.nil))
           )
      | _ => opaque
      end
     end
  end.

