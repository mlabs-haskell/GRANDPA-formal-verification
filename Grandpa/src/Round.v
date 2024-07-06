Require Import Blocks.                 
Require Import Votes.                  

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

