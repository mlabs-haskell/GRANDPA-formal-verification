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
Require Import OpaqueRound.
Require Import Protocol.State.
Require Import Protocol.StateMessages.
Require Import Protocol.FinalizedBlock.
Require Import Protocol.Protocol.
Require Import Protocol.Io.
Require Import Protocol.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Require Protocol.Proofs.Consistency.VoterStateExists.
Require Protocol.Proofs.Consistency.Rounds.Existence.
(**
If a [v:Voter] see that [b:AnyBlock] has supermajority in
the precommit votes of [r:OpaqueRound] at [t:Time],
then the same voter [v] agree that [b] has supermajority
at [(t2:Time) >= t].
*)

(*TODO: Maybe make this a folder and split the three results there?*)

Section Supermajority.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

(**
If a [v:Voter] see that [b:AnyBlock] has supermajority in
the precommit votes of [r:OpaqueRound] at [t:Time],
then the same voter [v] agree that [b] has supermajority
at [(t2:Time) >= t].
*)
Theorem supermajority_consistence `{io:Io}
  {b:AnyBlock}
  {v:Voter}
  (v_in_initial_state: VoterStateExists.IsParticipant v)
  {t t_increment : Time}
  {r_n: RoundNumber}
  {r_start:OpaqueRoundState}
  {r_end:OpaqueRoundState}
  (has_round_at_t:
    Existence.IsRoundAt v t r_n r_start
  )
  (has_round_at_t_plus_t_increment:
    Existence.IsRoundAt v (t+t_increment) r_n r_end
  )
  (has_supermajority_proof: Votes.block_has_supermajority b (get_all_prevote_votes r_start) = true)
  : Votes.block_has_supermajority b (get_all_prevote_votes r_end) = true.
(*TODO: Critical, especially for safety, for this:
  - Rounds Continuous  gave us that one round is update of the other
  - Extract that prevoter_votes sets must be related (the one in start is subset of the one in super_set)
  - Use the Voters module functions to conclude.
*)
Admitted.

End Supermajority.
