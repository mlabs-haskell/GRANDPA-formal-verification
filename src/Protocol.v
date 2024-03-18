Require Import Blocks.
Require Import Votes.
Require Import Preliminars.


Definition Time := nat.


Inductive RoundState 
      {preview_number precommit_number block_number}
  (preview_voters:Voters preview_number) 
  (precommit_voters: Voters precommit_number)
  (round_start_time:Time) 
  (last_block: Block block_number)
    : Time ->  Type :=
  | InitialRoundState 
    : RoundState preview_voters precommit_voters round_start_time last_block 0
  | RoundStateUpdate 
    {old_time_increment: Time}
    (old_state: RoundState 
      preview_voters precommit_voters 
      round_start_time last_block old_time_increment)
    (time_increment: Time)
    (new_preview_votes: Votes preview_voters last_block)
    (new_precommit_votes: Votes precommit_voters last_block)
    : RoundState preview_voters precommit_voters round_start_time last_block 
      (time_increment+ old_time_increment).


Definition get_preview_votes
  {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : 
  (Votes preview_voters last_block).
Admitted.

Definition get_precommit_votes
  {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : 
  (Votes precommit_voters last_block).
Admitted.


Variant Estimate {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : Type
  :=
    EstimateC 
    (new_block_number : nat)
    (new_block : Block new_block_number)
    (is_children: IsChildren new_block last_block)
    {g_block_number: nat}
    (g_preview: Block g_block_number)
    (g_preview_is_some : g ( get_preview_votes round_state) = Some g_preview)
    (new_block_is_children_of_g: IsChildren  new_block g_preview)
    : Estimate round_state.

Definition get_estimate {preview_number precommit_number : nat}
  {preview_voters : Voters preview_number} 
  {precommit_voters: Voters precommit_number}
  {round_time:Time}
  {round_number:nat}
  {last_block_number} 
  {last_block : Block last_block_number} 
  (round_state: RoundState preview_voters precommit_voters  round_time last_block round_number)
  : option (Estimate  round_state).
Admitted.


