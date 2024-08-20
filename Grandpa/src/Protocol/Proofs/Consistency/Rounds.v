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

Section ProtocolRound.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

(*
  We have tree main proofs here:
    - If a [v:Voter] sees [r:OpaqueRound] at some [t:Time],
      they see a [r2:RoundState] for [(t2:Time) >= t].
    - If a round exists at [t:Time], then at [(t2:Time) >= t] the round still
     exists [r2:OpaqueRound] and is a consistent update of
     [r] (ie [IsUpdateOf r r2]).
    - If a [v:Voter] see that [b:AnyBlock] has supermajority in
      the precommit votes of [r:OpaqueRound] at [t:Time],
      then the same voter [v] agree that [b] has supermajority
      at [(t2:Time) >= t].
*)


(*TODO: Maybe this is worthless*)
Definition HasRoundAt `{io:Io} (v:Voter) (t:Time) (rn:RoundNumber) :Prop :=
  exists r,
    get_voter_opaque_round (get_state_up_to t) v rn = Some r.


(**  Continuous_existence
   If a [v:Voter] sees [r:OpaqueRound] at some [t:Time],
      they see a [r2:RoundState] for [(t2:Time) >= t].
*)
Theorem continuous_existence `{io:Io}
  {v:Voter}
  (v_in_initial_state : VoterStateExists.IsParticipant v)
  :forall t t_increment rn,
      HasRoundAt v t rn
      -> HasRoundAt v (t+t_increment) rn.
(*TODO: Critical*)
Admitted.

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
    get_voter_opaque_round (get_state_up_to t) v r_n = Some r_start)
  (has_round_at_t_plus_t_increment:
    get_voter_opaque_round (get_state_up_to (t+t_increment)) v r_n = Some r_end)
  : IsUpdateOf r_start r_end.
(*TODO: critical*)
Admitted.


(**
If a [v:Voter] see that [b:AnyBlock] has supermajority in
the precommit votes of [r:OpaqueRound] at [t:Time],
then the same voter [v] agree that [b] has supermajority
at [(t2:Time) >= t].
*)
Theorem supermajority_consistence `{io:Io}
  {v:Voter}
  (v_in_initial_state: VoterStateExists.IsParticipant v)
  {t t_increment : Time}
  {r_n: RoundNumber}
  (r_start:OpaqueRoundState)
  (r_end:OpaqueRoundState)
  (has_round_at_t:
    get_voter_opaque_round (get_state_up_to t) v r_n = Some r_start)
  (has_round_at_t_plus_t_increment:
    get_voter_opaque_round (get_state_up_to (t+t_increment)) v r_n = Some r_end)
  : IsUpdateOf r_start r_end.
(*TODO: Critical, especially for safety*)
Admitted.

End ProtocolRound.
