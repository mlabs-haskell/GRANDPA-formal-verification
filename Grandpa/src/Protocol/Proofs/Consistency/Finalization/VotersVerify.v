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
Require Import Protocol.Io.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Require Protocol.Proofs.Consistency.VoterStateExists.

(**
  This module focus is to proof that every finalized blocks
  has supermajority after synchronisation.
*)


Section ProtocolFinalizationConsistency.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

(** Voter can confirm supermajority of any FinalizedBlock eventually.
  For all [fb:FinalizedBlock], and all [v:Voter],
   after enough [t_increment:Time] the voter see the votes
   that confirm the supermajority of the [fb].
*)
(*
  TODO: We May need to add as axiom that the origin block is
   has this.
*)
Theorem all_voters_verify_finalization_eventually `{io:Io}
  (fb:FinalizedBlock)
  (v:Voter)
  (v_participates_in_protocol:
    VoterStateExists.IsParticipant v)
  :
  let t_min := (fb.(FinalizedBlock.time) +  ((Time.from_nat 2) * global_time_constant) )
  in
  let r_n := fb.(FinalizedBlock.round_number)
  in
  forall t,
  t_min <= t  ->
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
