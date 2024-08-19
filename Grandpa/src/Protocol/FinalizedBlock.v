Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import VoterState.
Require Import Time.
Require Import RoundNumber.
Require Import OpaqueRound.


(** *FinalizedBlock

This type ties a finalized block with all the information
to identify the moment in witch the algorithm finalized the
block.
*)

Record FinalizedBlock := FinalizedBlockC {
  block : AnyBlock
  ;time:Time
  ;round_number:RoundNumber
  ;submitter_voter:Voter
  ;voters: Voters
  ;precommit_votes:Votes voters
  }.


Definition make_with_round
  (t:Time)
  (voter:Voter)
  (b:AnyBlock)
  (opaque:OpaqueRoundState)
  : FinalizedBlock
  := {|
  block := b
  ;time:=t
  ;round_number:= OpaqueRound.get_round_number opaque
  ;submitter_voter:=voter
  ;voters:=OpaqueRound.get_precommit_voters opaque
  ;precommit_votes:= OpaqueRound.get_all_precommit_votes opaque
  |}.
