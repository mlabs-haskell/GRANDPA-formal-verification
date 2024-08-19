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
Require Import DataTypes.List.Fold.
Require Import DataTypes.Option.
Require Import Protocol.State.
Require Import Protocol.StateMessages.
Require Import Protocol.FinalizedBlock.
Require Import Protocol.Protocol.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.


Require Import Protocol.Io.
Require Import Protocol.

Section ProtocolFinalizationConsistency.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.



Theorem all_voters_verify_finalization `{io:Io}
  (fb:FinalizedBlock)
  (v:Voter)
  (v_participates_in_protocol:
    exists vs,  get_voter_state v initial_state = Some vs)
  :
  let t_min := (fb.(FinalizedBlock.time) +  ((Time.from_nat 2) * global_time_constant) )
  in
  let r_n := fb.(FinalizedBlock.round_number)
  in
  forall t,
  t >= t_min ->
  let state := get_state_up_to t
  in
  (exists r, get_voter_opaque_round state v r_n = Some r
    /\
      Votes.block_has_supermajority
        fb.(FinalizedBlock.block)
        (OpaqueRound.get_all_prevote_votes r)
      = true
  ).
  (*TODO: critical
  Proof by stating the same thing but only for t_min
  and use the fact that the rounds are monotone (ie
     they grow over time and are consistent with
     previous states
   *)
  Admitted.

End ProtocolFinalizationConsistency.
