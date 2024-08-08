Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import VoterState.
Require Import Time.
Require Import RoundNumber.


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

(* TODO: 
   Maybe add make_with_round : Vote -> AnyBlock -> Round -> FinalizedBlock.
 *)
