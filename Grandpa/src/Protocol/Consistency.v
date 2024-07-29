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
Require Import Protocol.State.
Require Import Protocol.StateMessages.
Require Import Protocol.FinalizedBlock.
Require Import Protocol.Protocol.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.


Require Import Protocol.Io.

Section ProtocolConsistency.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Lemma produce_states_unfold_0 `{io:Io}
  : get_state_up_to (Time.from_nat 0)  
   = 
    make_initial_state_from (io_get_round_voters (RoundNumber.from_nat 0)).
Proof.
  unfold get_state_up_to.
  unfold get_last.
  simpl.
  reflexivity.
Qed.

Lemma initial_state_message_count_is_0 
  `{io:Io}
  :
  State.message_count 
    (make_initial_state_from 
      (io_get_round_voters 
        (RoundNumber.from_nat 0)
      )
    ) =0.
Proof.
  remember (io_get_round_voters (RoundNumber.from_nat 0)) as state0_dict eqn:eq_state0.
  destruct state0_dict as [state0_list].
  unfold make_initial_state_from.
  Opaque map.
  simpl.
  Transparent map.
  remember (
process_round_voters_from
       (Dictionary.DictionaryC Voter VoterKind state0_list)
  ) as dummy.
  destruct dummy.
  destruct p.
  reflexivity.
Qed.

Lemma initial_state_pending_messages_empty 
  `{io:Io}
  :
  State.pending_messages
    (make_initial_state_from 
      (io_get_round_voters 
        (RoundNumber.from_nat 0)
      )
    ) = Dictionary.empty .
Proof.
  remember (io_get_round_voters (RoundNumber.from_nat 0)) as state0_dict eqn:eq_state0.
  destruct state0_dict as [state0_list].
  unfold make_initial_state_from.
  Opaque map.
  simpl.
  Transparent map.
  remember (
process_round_voters_from
       (Dictionary.DictionaryC Voter VoterKind state0_list)
  ) as dummy.
  destruct dummy.
  destruct p.
  reflexivity.
Qed.

Lemma update_vote_for_voter_dont_touch_messages `{io:Io}
  (t:Time)
  (v:Voter)
  (s:State)
  : forall m, State.pending_messages (update_vote_for_voter t v s m) = State.pending_messages s.
Proof.
  intro m.
  simpl.
  unfold update_vote_for_voter.
  destruct (is_message_processed_by s m v).
  - reflexivity.
  - destruct (io_accept_vote t m v).
    + unfold accept_vote.
      destruct (Dictionary.lookup v (voters_state s)).
      * reflexivity.
      * reflexivity.
    + destruct (
        PeanoNat.Nat.leb (NatWrapper.to_nat t)
          (NatWrapper.to_nat (Message.time m + global_time_constant))
        || (v =? voter m)
        ).
      * unfold accept_vote.
        destruct (Dictionary.lookup v (voters_state s)).
        ++ reflexivity.
        ++ reflexivity.
      * reflexivity.
Qed.

Lemma update_votes_for_voter_dont_touch_messages_aux `{io:Io}
  (t:Time)
  (v:Voter)
  : forall l s, State.pending_messages (List.fold_left (update_vote_for_voter t v) l s) = State.pending_messages s.
Proof.
  intros l.
  induction l.
  - reflexivity.
  - simpl.
    intro s.
    pose (IHl (update_vote_for_voter t v s a)) as H.
    rewrite H.
    apply update_vote_for_voter_dont_touch_messages.
Qed.


(*
  TODO: As this shows, messages aren't mark as processed!, so no collection of them!
*)
Lemma update_votes_for_voter_dont_touch_messages `{io:Io}
  (t:Time)
  (v:Voter)
  (s:State)
  : State.pending_messages (upate_votes_for_voter t s v) = State.pending_messages s.
Proof.
  unfold upate_votes_for_voter.
  apply update_votes_for_voter_dont_touch_messages_aux.
Qed.
  
Lemma voter_state_continuos_existence_step_1 `{io:Io}
  (v:Voter)
  (
    is_some_at_0
    : exists vs1
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to (Time.from_nat 0))) = Some vs1
  )
    : exists vs2
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to (Time.from_nat 1) )) = Some vs2.
Proof.
  destruct is_some_at_0 as [vs H].
  simpl.
  unfold get_state_up_to.
  unfold get_state_up_to in H.
  remember (make_initial_state_from (io_get_round_voters (RoundNumber.from_nat 0))) as state0 eqn:eq_state0.
  unfold produce_states.
  unfold produce_states in H.
  unfold get_last.
  unfold get_last in H.
  simpl.
  simpl in H.
  unfold update_votes.
  unfold prune_messages.
  unfold prune_message.
  unfold upate_votes_for_voter.
  unfold update_vote_for_voter.
  unfold accept_vote.
  simpl.
  Admitted.


Lemma voter_state_continuos_existence_step `{io:Io}
  (v:Voter)
  (t: Time)
  (
    is_some_at_t
    : exists vs1
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to t)) = Some vs1
  )
    : exists vs2
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to ((Time.from_nat 1)+t)%natWrapper )) = Some vs2.
Proof.
  destruct is_some_at_t as [vs H].
  destruct t as [t0].
  induction t0.
  - apply voter_state_continuos_existence_step_1.
    eauto.
  - 
  Admitted.

Lemma voter_state_continuos_existence `{Io}
  (v:Voter)
  (t: Time)
  (
    is_some_at_t
    : exists vs1
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to t)) = Some vs1
  )
  (t_increment:Time)
    : exists vs2
      , Dictionary.lookup 
        v 
        (voters_state (get_state_up_to (t_increment+t)%natWrapper )) = Some vs2.
Proof.
  Admitted.

Lemma round_continuos_existence `{Io}
  (v:Voter)
  (t: Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    : State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
    : exists r2
    , State.get_voter_opaque_round (get_state_up_to (t_increment+t)) v r_n = Some r2.
Proof.
  Admitted.

Lemma round_prevoters_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  State.get_voter_opaque_round 
    (get_state_up_to (t_increment+t))
    v 
    r_n 
    = Some r2 
  /\ (OpaqueRound.get_prevote_voters r2 = OpaqueRound.get_prevote_voters r1).
Proof.
  destruct (round_continuos_existence v t r_n r1 is_some_at_t t_increment)
    as [r2 is_some].
  exists r2.
  split.
  apply is_some.
  induction t_increment.
  Admitted.
  (*
  - simpl in is_some.
    rewrite is_some in is_some_at_t.
    injection is_some_at_t.
    intro eq_r.
    rewrite  eq_r.
    reflexivity.
  - Admitted.
  *)

Lemma round_precommiters_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  :exists r2,
  State.get_voter_opaque_round 
    (get_state_up_to (t_increment+t))
    v 
    r_n 
    = Some r2 
  /\ (OpaqueRound.get_precommit_voters r2 = OpaqueRound.get_precommit_voters r1).
Admitted.

Lemma round_precomits_consistent_over_time `{Io}
  (v:Voter)
  (t:Time)
  (r_n:RoundNumber)
  (r1:OpaqueRound.OpaqueRoundState)
  (
    is_some_at_t
    :State.get_voter_opaque_round (get_state_up_to t) v r_n = Some r1
  )
  (t_increment:Time)
  (r2:OpaqueRound.OpaqueRoundState)
  (is_some_at_t_increment: 
    State.get_voter_opaque_round 
      (get_state_up_to (t_increment+t))
      v 
      r_n 
      = Some r2
  )
  (voters_are_equal: (OpaqueRound.get_precommit_voters r1) = (OpaqueRound.get_precommit_voters r2))
  : (Votes.cast voters_are_equal (OpaqueRound.get_all_precommit_votes r1) = OpaqueRound.get_all_precommit_votes r2).
Admitted.

Lemma finalized_blocks_monotone_over_time `{Io}
  (t:Time)
  (t_increment:Time)
  : exists  l, 
  (global_finalized_blocks (get_state_up_to (t_increment + t)))
  =
  l ++ (global_finalized_blocks (get_state_up_to t)).
Proof.
  Admitted.

Lemma finalized_blocks_monotone_over_time2 `{Io}
  (t:Time)
  (t_increment:Time)
  : forall b, List.In b (global_finalized_blocks (get_state_up_to t))
  ->
  List.In b (global_finalized_blocks (get_state_up_to (t_increment + t))).
Proof.
  Admitted.

(*
Lemma votes_are_monotone_over_time `{Io}
  (v:Voter)
  (t1 t2:Time)
  (r_n:nat)
  (related_t:t1 <= t2)
  (state_is_from_protocol: get_state_up_to t)
  (b_in
    :List.In 
      (to_any b) 
      (List.map ( fun x => fst (fst x)) (global_finalized_blocks state))
  )
  .
*)

Lemma finalized_block_time_leq
  (t:Time)
  (fb: FinalizedBlock.FinalizedBlock)
  `{Io}
  (b_in
    :List.In 
      fb
      (global_finalized_blocks (get_state_up_to t))
  )
  : fb.(FinalizedBlock.time) <= t.
Admitted.

Lemma finalized_block_came_from_voter
  (t:Time)
  (fb: FinalizedBlock.FinalizedBlock)
  `{Io}
  (b_in
    :List.In 
      fb
      (global_finalized_blocks (get_state_up_to t))
  )
  :exists (r:OpaqueRound.OpaqueRoundState)
    , State.get_voter_opaque_round (get_state_up_to fb.(FinalizedBlock.time)) fb.(FinalizedBlock.submitter_voter) fb.(FinalizedBlock.round_number)
      = Some r
    /\ 
      g 
        (OpaqueRound.get_all_precommit_votes 
          r
        ) = Some fb.(FinalizedBlock.block) .
Proof.
  Admitted.


(*TODO: add consistency of total_number_of_voters param
  that is passed to both prevote and precommit set of voters for every round
*)
  
End ProtocolConsistency.
