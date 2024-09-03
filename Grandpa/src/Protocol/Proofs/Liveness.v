Require Import Voter.
Require Import Time.
Require Import RoundNumber.
Require Import State.
Require Import Protocol.Protocol.
Require Import Estimate.
Require Import OpaqueRound.
Require Import Votes.
Require Import AnyBlock.

(*
Lemma lemma_4_4 
  {Io}
  (v1 v2 : Voter)
  (t1 t2 : Time)
  (rn : RoundNumber)
  (s1 s2 : State)
  (s1_at_t1 : s1 = get_state_up_to t1)
  (s2_at_t2 : s2 = get_state_up_to t2)
  (or1 or2:OpaqueRoundState)
  (or1_from_s1 : Some or1 = get_voter_opaque_round s1 v1 rn)
  (or2_from_s2 : Some or2 = get_voter_opaque_round s2 v2 rn)
  (prevote_subset: VotesIsSubset (OpaqueRound.get_all_prevote_votes or1) (OpaqueRound.get_all_prevote_votes or2) )
  (precommit_subset: VotesIsSubset (OpaqueRound.get_all_precommit_votes or1) (OpaqueRound.get_all_precommit_votes or2) )
  (e1 e2 : AnyBlock)
  :bool.
*)
