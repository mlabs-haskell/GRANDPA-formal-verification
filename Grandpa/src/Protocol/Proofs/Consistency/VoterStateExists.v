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

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.


Require Import Protocol.Io.
Require Import Protocol.

Section ProtocolVoterStateExistsConsistency.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Definition IsParticipant `{io:Io} (v:Voter) :Prop :=
  exists vs, get_voter_state v initial_state = Some vs.

Theorem voter_state_exists_always `{io:Io}
  (v:Voter)
  (v_in_initial_state : IsParticipant v)
  :forall t, exists vs, get_voter_state v (get_state_up_to t) = Some vs.
(*TODO: Critical? This maybe used in other theorems*)
Admitted.


End ProtocolVoterStateExistsConsistency.
