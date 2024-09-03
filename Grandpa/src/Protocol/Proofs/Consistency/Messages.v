Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import State.
Require Import Time.
Require Import RoundNumber.
Require Import Preliminars.
Require Import DataTypes.List.Count.
Require Import DataTypes.List.Fold.
Require Import DataTypes.Sets.
Require Import Protocol.FinalizedBlock.
Require Import Protocol.Io.
Require Import Protocol.Protocol.
Require Import Message.

Require Import PeanoNat.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Classes.Math.Semigroup.
Require Import Instances.List.

Require Protocol.Proofs.Consistency.old_consistency.
Require Protocol.Proofs.Consistency.Rounds.Existence.
Require Protocol.Proofs.Consistency.Rounds.Continuous.
Require Protocol.Proofs.Consistency.Rounds.Supermajority.
Require Protocol.Proofs.Consistency.Finalization.SubmmiterFinalized.
Require Protocol.Proofs.Consistency.Finalization.VotersVerify.


(*
This module objective is to show that a message is issued at the time it was send.
*)

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.


(*
Lemma message_send_at_round `{io:Io}
  (t:Time)
  (message:Message)
  :
  let
    state  :=
      get_state_up_to t
  in
    (*TODO:More or less, we need to replace = here and instead use a custom equality*)
    Dictionary.lookup message.(Message.voter) message.(Message.pending_messages) = message
    (*TODO: complete this, it express the fact that the correct voter at the correct time and
      and round issued the message
    *)
    -> False
  .


*)



Close Scope bool.
Close Scope list.
Close Scope eqb.
Close Scope math.
Close Scope natWrapper.
