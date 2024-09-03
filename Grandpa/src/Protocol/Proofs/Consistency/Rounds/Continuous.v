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
If a [v:Voter] sees [r:OpaqueRound] at some [t:Time],
they see a [r2:RoundState] for [(t2:Time) >= t].
*)

Section Continuous.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.



(** All [RoundState] of same round are related
If a round exists at [t:Time], then at [(t2:Time) >= t] the round still
exists [r2:OpaqueRound] and is a consistent update of
[r] (ie [IsUpdateOf r r2]).
*)
Theorem rounds_are_updates `{io:Io}
  {v:Voter}
  (v_in_initial_state: VoterStateExists.IsParticipant v)
  {t t_increment : Time}
  {r_n: RoundNumber}
  (r_start:OpaqueRoundState)
  (r_end:OpaqueRoundState)
  (has_round_at_t:
    Existence.IsRoundAt v t r_n r_start
  )
  (has_round_at_t_plus_t_increment:
    Existence.IsRoundAt v (t+t_increment) r_n r_end
  )
  : IsUpdateOf r_start r_end.
(*TODO: critical*)
Admitted.

End Continuous.
