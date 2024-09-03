Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import Voters.
Require Import Round.
Require Import Estimate.

Require Import Coq.Program.Equality.

Export Round.

Require Import Message.

Require Import Classes.Math.All.

(** *OpaqueRoundState
This didn't exist in the paper, is a convenient newtype around [RoundState].

The [OpaqueRoundState] type allow us to store different rounds in a single
collection like a [vector] or a [list].

Another advantage is that we don't need to explicitly pass around the
parameters of a round.
*)

Variant OpaqueRoundState: Type :=
  | OpaqueRoundStateC {total_voters round_number}
    {prevote_voters:Voters}
    {precommit_voters: Voters}
    {round_start_time:Time}
    {time:Time}
    (round_state:
      RoundState
        total_voters
        prevote_voters
        precommit_voters
  round_start_time
        round_number
        time
    ).

Definition get_prevote_voters (o:OpaqueRoundState) : Voters
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_prevote_voters r
  end.

Definition get_precommit_voters (o:OpaqueRoundState) : Voters
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_precommit_voters r
  end.

Definition get_start_time (o:OpaqueRoundState) : Time
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_start_time r
  end.

Definition get_time_increment (o:OpaqueRoundState) : Time
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_time_increment r
  end.

Definition get_round_number (o:OpaqueRoundState) : RoundNumber
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_round_number r
  end.

Definition get_total_voters (o:OpaqueRoundState) : nat
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_total_voters r
  end.

Definition get_all_prevote_votes (o:OpaqueRoundState) : (Votes (get_prevote_voters o))
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_prevote_votes r
  end.

Definition get_all_precommit_votes (o:OpaqueRoundState) : (Votes (get_precommit_voters o))
  :=
  match o with
  | OpaqueRoundStateC r => Round.get_precommit_votes r
  end.

Definition is_completable (o:OpaqueRoundState)
  : bool
  :=
  match o with
  | OpaqueRoundStateC r => Estimate.is_completable r
  end.

Definition get_estimate (o:OpaqueRoundState)
  : option AnyBlock
  :=
  match o with
  | OpaqueRoundStateC r => Estimate.get_estimate r
  end.


Open Scope math.
Open Scope natWrapper.

Program Definition update_opaque_round_state
  (o:OpaqueRoundState)
  (time_increment:Time)
  (new_prevotes: Votes (get_prevote_voters o))
  (new_precommits:Votes (get_precommit_voters o))
  : OpaqueRoundState
  :=
  match o with
  | @OpaqueRoundStateC
      total_voters
      round_number
      prevote_voters
      precommit_voters
      start_time
      time
      r =>
        OpaqueRoundStateC(
          Round.RoundStateUpdate
          total_voters
          prevote_voters
          precommit_voters
          start_time
          round_number
          r
          time_increment
          new_prevotes
          new_precommits
        )
  end.

(**
It add the precommit or prevote vote represented
by a message to the particular round it is related to.

If the message came from a voter outside of the set of
precommiters or prevoters for the round, we ignore the vote.
In the paper they assumed that every participant is capable
to determine the round participants.

If the message isn't a precommit or prevote we do nothing.
*)
Definition update_votes_with_msg
  (opaque:OpaqueRoundState)
  (msg:Message)
  : OpaqueRoundState
  :=
  match opaque with
  | OpaqueRoundStateC r =>
    let new_time_increment : Time := (msg.(Message.time) - (get_start_time opaque + get_time_increment opaque))
    in
    match Message.message_to_prevote_vote msg (get_prevote_voters opaque)with
    | Some new_votes =>
        update_opaque_round_state opaque new_time_increment
           (VotesC (get_prevote_voters opaque) (List.cons new_votes List.nil))
           (VotesC (get_precommit_voters opaque) List.nil)
    | _ =>
      match Message.message_to_precommit_vote msg (get_precommit_voters opaque) with
      | Some new_votes =>
        update_opaque_round_state opaque new_time_increment
             (VotesC (get_prevote_voters opaque) List.nil)
             (VotesC (get_precommit_voters opaque) (List.cons new_votes List.nil))
      | _ => opaque
      end
     end
  end.


Section IsUpdateRelation.

Inductive IsUpdateOf : OpaqueRoundState -> OpaqueRoundState -> Prop
  :=
  | SameRoundState o : IsUpdateOf o o
  | IsRoundUpdate o1 o2 (is_related : IsUpdateOf o1 o2)
      (time_increment:Time)
      (new_prevotes: Votes (get_prevote_voters o2))
      (new_precommits:Votes (get_precommit_voters o2))
      : IsUpdateOf o1 (update_opaque_round_state o2 time_increment new_prevotes new_precommits).


Lemma is_update_reflexivity o : IsUpdateOf o o.
Proof.
  apply SameRoundState.
Qed.

Lemma origin_isnt_update_of_not_origin
    {total_voters round_number}
    {prevote_voters:Voters}
    {precommit_voters: Voters}
    {round_start_time:Time}
    {time:Time}
    o
      (time_increment:Time)
      (new_prevotes: Votes (get_prevote_voters o))
      (new_precommits:Votes (get_precommit_voters o))
    : IsUpdateOf (update_opaque_round_state o time_increment new_prevotes new_precommits) (OpaqueRoundStateC (InitialRoundState total_voters prevote_voters precommit_voters round_start_time round_number)) -> False.
Proof.
  intro H.
  destruct o.
  inversion H.
  destruct o2.
  inversion H2.
Qed.


Lemma is_update_of_previous o1 o2 :
  forall ti npv npr,
  IsUpdateOf (update_opaque_round_state o1 ti npv npr) o2
  -> IsUpdateOf o1 o2.
Proof.
  destruct o2.
  intros *.
  intro H.
  Opaque update_opaque_round_state.
  induction round_state.
  - destruct o1.
    exfalso. eapply origin_isnt_update_of_not_origin. eauto.
  Admitted.


Lemma is_update_transitive {o1} o2
  : IsUpdateOf o1 o2
  -> (forall {o3}, IsUpdateOf o2 o3
    -> IsUpdateOf o1 o3).
Proof.
  intro H.
  induction H.
  - auto.
  - intros o3 H2.
    apply IHIsUpdateOf.
    eapply (is_update_of_previous o2 o3).
    apply H2.
Qed.

Lemma is_update_has_same_prevote_voters o1 o2
  (is_update: IsUpdateOf o1 o2)
  : get_prevote_voters o1 = get_prevote_voters o2.
Proof.
  induction is_update.
  - auto.
  - destruct o1.
    destruct o2.
    auto.
Qed.

Lemma is_update_has_same_precommit_voters o1 o2
  (is_update: IsUpdateOf o1 o2)
  : get_precommit_voters o1 = get_precommit_voters o2.
Proof.
  induction is_update.
  - auto.
  - destruct o1.
    destruct o2.
    auto.
Qed.

Lemma update_votes_with_msg_is_update_of o msg
  : IsUpdateOf o (update_votes_with_msg o msg).
Proof.
  destruct o.
  Opaque update_opaque_round_state.
  simpl.
  Transparent update_opaque_round_state.
  destruct (message_to_prevote_vote msg (Round.get_prevote_voters round_state)).
  - apply IsRoundUpdate.
    apply SameRoundState.
  - destruct (message_to_precommit_vote msg (Round.get_precommit_voters round_state)).
    + apply IsRoundUpdate.
      apply SameRoundState.
    + apply SameRoundState.
Qed.

End IsUpdateRelation.


Close Scope natWrapper.
Close Scope math.
