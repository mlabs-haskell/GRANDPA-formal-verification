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

(**
If a [v:Voter] sees [r:OpaqueRound] at some [t:Time],
they see a [r2:RoundState] for [(t2:Time) >= t].
*)

Section Existence.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Definition IsRoundAt `{io:Io} (v:Voter) (t:Time) (rn:RoundNumber) (r:OpaqueRoundState) :Prop :=
    get_voter_opaque_round (get_state_up_to t) v rn = Some r.


(**  Continuous_existence
   If a [v:Voter] sees [r:OpaqueRound] at some [t:Time],
      they see a [r2:RoundState] for [(t2:Time) >= t].
*)
Theorem continuous_existence `{io:Io}
  {v:Voter}
  (v_in_initial_state : VoterStateExists.IsParticipant v)
  :forall t t_increment rn,
      exists r, IsRoundAt v t rn r
      -> exists r2, IsRoundAt v (t+t_increment) rn r2.
(*TODO: Critical*)
Admitted.

End Existence.
