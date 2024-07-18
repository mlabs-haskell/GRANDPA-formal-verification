Require Import Blocks.Block.
Require Import Voters. 
Require Import Votes.
Require Import Voter.


Definition Time := nat.

Inductive RoundState
  (total_voters:nat)
  (prevote_voters:Voters ) 
  (precommit_voters: Voters )
  (round_start_time:Time) 
  (round_number: nat)
  : Time ->  Type :=
  | InitialRoundState 
    : RoundState total_voters prevote_voters precommit_voters round_start_time round_number 0
  | RoundStateUpdate 
    {old_time_increment: Time}
    (old_state: RoundState total_voters
      prevote_voters precommit_voters 
      round_start_time round_number old_time_increment)
    (time_increment: Time)
    (new_prevote_votes: Votes prevote_voters)
    (new_precommit_votes: Votes precommit_voters)
    : RoundState total_voters prevote_voters precommit_voters round_start_time
      round_number
      (time_increment+ old_time_increment).

Section State1.

Context {total_voters:nat}.
Context {prevote_voters:Voters  }.
Context {precommit_voters: Voters }.
Context {round_time : Time}.
Context {round_number: nat}.
Context {time_increment: nat}.




Definition get_prevote_votes
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : 
  (Votes prevote_voters )
  := 
  match round_state with
  | InitialRoundState _ _ _ _ _ => VotesC _ List.nil 
  | RoundStateUpdate _ _ _ _ _ _ _ new_prevote_votes _ => new_prevote_votes
  end.

Definition get_precommit_votes
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : 
  (Votes precommit_voters )
  :=
  match round_state with
  | InitialRoundState _ _ _ _ _=> VotesC _ List.nil (* No votes in initial round state *)
  | RoundStateUpdate _ _ _ _ _ _ _ _ new_precommit_votes => new_precommit_votes
  end.
  

Definition get_prevote_voters
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  :Voters 
  := prevote_voters.

Definition get_precommit_voters
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  :Voters 
  := precommit_voters.

Definition get_start_time 
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : Time
  := round_time.

Definition get_round_number
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : nat
  := round_number.

Definition get_time_increment
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : Time
  := time_increment.

Definition get_total_voters
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : nat
  := total_voters.

End State1.


Fixpoint get_all_prevote_votes
  {total_voters:nat}
  {prevote_voters : Voters } 
  {precommit_voters: Voters }
  {round_time:Time}
  {round_number:nat}
  {time_increment: Time}
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : 
  (Votes prevote_voters )
  := 
  match round_state with
  | InitialRoundState _ _ _ _ _ => VotesC _ List.nil 
  | RoundStateUpdate _ _ _ _ _ old_state  _ new_prevote_votes _ => mergeVotes (get_all_prevote_votes old_state) new_prevote_votes
  end.

Fixpoint get_all_precommit_votes
  {total_voters:nat}
  {prevote_voters : Voters } 
  {precommit_voters: Voters }
  {round_time:Time}
  {round_number:nat}
  {time_increment: Time}
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : 
  (Votes precommit_voters )
  := 
  match round_state with
  | InitialRoundState _ _ _ _ _=> VotesC _ List.nil 
  | RoundStateUpdate _ _ _ _ _ old_state  _ _ new_precommit_votes => mergeVotes (get_all_precommit_votes old_state) new_precommit_votes
  end.

Definition voter_voted_in_prevote
  {total_voters:nat}
  {prevote_voters : Voters } 
  {precommit_voters: Voters }
  {round_time:Time}
  {round_number:nat}
  {time_increment: Time}
  (voter:Voter)
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : 
  bool
  := 
  let prevote_votes := get_all_prevote_votes round_state
  in
    if Voters.inb voter prevote_voters 
    then voter_voted_in_votes voter prevote_votes
    else true.

Definition  voter_voted_in_precommit 
  {total_voters:nat}
  {prevote_voters : Voters } 
  {precommit_voters: Voters }
  {round_time:Time}
  {round_number:nat}
  {time_increment: Time}
  (voter:Voter)
  (round_state: RoundState total_voters prevote_voters precommit_voters  round_time  round_number time_increment)
  : 
  bool
  := 
  let precommit_votes := get_all_precommit_votes round_state
  in
    if Voters.inb voter precommit_voters 
    then voter_voted_in_votes voter precommit_votes
    else true.

