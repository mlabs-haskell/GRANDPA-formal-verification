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

Section ProtocolConsistency.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

(*TODO: Deprecated, we keep all them here until we find the right module
  to put them on.
*)

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

Lemma get_state_up_to_0_is_initial_state `{Io}
  :
  let state_0 :=
    (make_initial_state_from
      (io_get_round_voters
        (RoundNumber.from_nat 0)
      )
    )
  in
    get_state_up_to (Time.from_nat 0)
    =
    state_0.
Proof.
  auto.
Qed.


Definition ContinueVoterStates {A B} (f:A->A) (g:A -> Dictionary.Dictionary Voter B)
  (v:Voter)
  :=
  forall a
    , is_some (Dictionary.lookup v (g a)) = true
    <-> is_some (Dictionary.lookup v (g (f a)))=true.

Lemma is_some_iff_some {A} (x:option A)
  : is_some x = true <-> exists w, x = Some w.
Proof.
  split.
  - intro H.
    destruct x.
    + eauto.
    + inversion H.
  - intros [w H].
    rewrite H.
    auto.
Qed.

Lemma not_is_some_iff_none {A} (x:option A)
  : is_some x = false <-> x = None.
Proof.
split.
- intros H.
  destruct x.
  + inversion H.
  + auto.
- intros H.
  rewrite H.
  auto.
Qed.


Lemma accept_vote_continues_voter_state `{io:Io}
  (voter:Voter)
  (m:Message)
  :
  ContinueVoterStates (fun s => accept_vote s voter m) State.voters_state voter.
Proof.
  intros state.
  split.
  - unfold accept_vote.
    intro H.
    apply is_some_iff_some in H.
    destruct H as [old_vs H].
    rewrite H.
    unfold update_voter_state.
    simpl.
    apply is_some_iff_some.
    exists (update_with_msg old_vs m).
    apply Dictionary.add_really_adds.
  - Admitted.



Lemma voter_state_continuos_existence_in_accept_vote `{io:Io}
  (state:State)
  (voter1 voter2:Voter)
  (m:Message)
  (is_some_at_state: is_some (Dictionary.lookup voter1 state.(voters_state)) = true)
  :
    is_some (Dictionary.lookup voter1 (accept_vote state voter2 m).(voters_state)) = true.
Proof.
  unfold accept_vote.
  destruct (Dictionary.lookup voter2 state.(State.voters_state)).
  2: auto.
  simpl.
  destruct (voter1 =? voter2) eqn:v1_eqb_v2.
  - rewrite is_some_iff_some.
    exists (update_with_msg v m).
    apply Dictionary.add_really_adds_eqb_k.
    auto.
  - pose (Dictionary.lookup_add_result state.(State.voters_state) voter1 voter2 (update_with_msg v m)) as H.
    destruct H as [ [eq_voters H  ] | ].
    + rewrite eq_voters in v1_eqb_v2. discriminate v1_eqb_v2.
    + rewrite is_some_iff_some.
      rewrite is_some_iff_some in is_some_at_state.
      destruct is_some_at_state as [w H_is_some].
      rewrite H_is_some in H.
      destruct H as [_ H].
      eauto.
Qed.

Lemma voter_state_continuos_existence_in_update_vote_for_voter `{io:Io}
  (t:Time)
  (voter1 voter2:Voter)
  (state:State)
  (m:Message)
  (is_some_at_state:
    is_some (Dictionary.lookup voter1 state.(voters_state)) = true)
  :
  is_some (
    Dictionary.lookup
      voter1
      (StateMessages.update_vote_for_voter t voter2 state m).(voters_state)
  ) = true.
Proof.
  unfold update_vote_for_voter.
  destruct (is_message_processed_by state m voter2).
  - auto.
  - destruct (io_accept_vote t m voter2).
    + eauto using voter_state_continuos_existence_in_accept_vote.
    + destruct (
         PeanoNat.Nat.leb (NatWrapper.to_nat t)
           (NatWrapper.to_nat (Message.time m + global_time_constant))
         || (voter2 =? Message.voter m)
      );
      eauto using voter_state_continuos_existence_in_accept_vote.
Qed.

Lemma voter_state_continuos_existence_in_update_votes_for_voter `{io:Io}
  (t:Time)
  (voter1 voter2:Voter)
  (state:State)
  (is_some_at_state:
    is_some (Dictionary.lookup voter1 state.(voters_state))  = true
  )
  :
   is_some
    (Dictionary.lookup
        voter1
        (StateMessages.update_votes_for_voter t state voter2).(voters_state)
    )
   =
   true.
Proof.
  unfold update_votes_for_voter.
  apply fold_left_preserves_property.
  - eauto.
  - intros state2 m2 H2.
    destruct (voter_state_continuos_existence_in_update_vote_for_voter t voter1 voter2 state2 m2 H2).
    +  reflexivity.
Qed.

Lemma voter_state_continuos_existence_in_prune_message `{io:Io}
  (voter:Voter)
  (m:Message)
  (state:State)
  (is_some_at_state:
    is_some (Dictionary.lookup voter state.(State.voters_state))  = true
  )
  :
    is_some
      (Dictionary.lookup voter (prune_message state m).(State.voters_state))
    =
    true.
Proof.
  unfold prune_message.
  destruct (
    List.fold_left
      (fun (acc : bool) (v : Voter) =>
       acc && is_message_processed_by state m v)
      get_all_time_participants true
  );eauto.
Qed.

Lemma prune_message_continues_voter_state_existence `{io:Io}
  (voter:Voter)
  (m:Message)
  :ContinueVoterStates (fun s => prune_message s m) State.voters_state voter.
Proof.
  intro state.
  split.
  - apply voter_state_continuos_existence_in_prune_message.
  - intros H.
    unfold prune_message in  H.
    destruct (
      List.fold_left
        (fun (acc : bool) (v : Voter) =>
         acc && is_message_processed_by state m v)
        get_all_time_participants true
    );eauto.
Qed.

Lemma voter_state_continuos_existence_in_prune_messages `{io:Io}
  (voter:Voter)
  (state:State)
  (is_some_at_state:
    is_some (Dictionary.lookup voter state.(State.voters_state)) = true
  )
  :
    is_some
      (Dictionary.lookup voter (prune_messages state).(State.voters_state))
    =
    true.
Proof.
  unfold prune_messages.
  apply fold_left_preserves_property.
  - eauto.
  - eauto using voter_state_continuos_existence_in_prune_message.
Qed.



Lemma prune_messages_continues_voter_state_existence `{io:Io}
  (voter:Voter)
  :
  ContinueVoterStates prune_messages State.voters_state voter.
Proof.
  intros state.
  split.
  - apply voter_state_continuos_existence_in_prune_messages.
  - intros H.
    unfold prune_messages in H.
    destruct (Dictionary.lookup voter (voters_state state)) eqn:result_voter.
    + auto.
    + simpl.
      enough (
        (Dictionary.lookup voter
         (voters_state
            (List.fold_left prune_message
               (List.map snd (Dictionary.to_list (pending_messages state)))
               state))) = None
      ).
      * rewrite <- not_is_some_iff_none in H0.
        rewrite <- H.
        rewrite <- H0.
        auto.
      * apply fold_left_preserves_property .
        ++ auto.
        ++ intros state2 m Hnone.
           destruct (Dictionary.lookup voter (voters_state (prune_message state2 m))) eqn:H3.
           --
            pose (prune_message_continues_voter_state_existence voter m state2) as H2.
            rewrite is_some_iff_some in H2.
            rewrite is_some_iff_some in H2.
            destruct H2 as [ _ H2].
            destruct H2 as [v2 H2].
            +++ eauto.
            +++ exfalso.
                rewrite Hnone in H2.
                inversion H2.
          -- auto.
Qed.


Lemma voter_state_continuos_existence_in_update_votes `{io:Io}
  (t:Time)
  (voter:Voter)
  (state:State)
  (is_some_at_state:
    is_some (Dictionary.lookup voter state.(voters_state)) = true
  )
  :
    is_some (Dictionary.lookup
        voter
        (StateMessages.update_votes t state).(voters_state) )
      =
      true.
Proof.
  unfold update_votes.
  apply voter_state_continuos_existence_in_prune_messages.
  apply fold_left_preserves_property.
  - eauto.
  - intros state2 voter2 H.
    pose (voter_state_continuos_existence_in_update_votes_for_voter t voter voter2 state2).
    apply e.
    auto.
Qed.



Lemma voter_state_continuos_existence_in_voters_round_step `{io:Io}
  (v:Voter)
  (state:State)
  (t:Time)
  (
    is_some_at_state
    : is_some (
       Dictionary.lookup
        v
        (voters_state state)
      )= true
  )
    : is_some (
        Dictionary.lookup
        v
        (voters_state ( voters_round_step t state))
      ) = true.
Proof.
  Admitted.



Lemma voter_state_continuos_existence_step_1 `{io:Io}
  (v:Voter)
  (
    is_some_at_0
    : is_some(
        Dictionary.lookup
        v
        (voters_state (get_state_up_to (Time.from_nat 0)))
        )= true
  )
    : is_some(
        Dictionary.lookup
        v
        (voters_state (get_state_up_to (Time.from_nat 1) ))
        ) = true.
Proof.
  cbn.
  apply voter_state_continuos_existence_in_voters_round_step.
  apply voter_state_continuos_existence_in_update_votes.
  auto.
Qed.


Lemma get_state_up_to_unfold `{io:Io} (t:Time)
  :
  let new_t := Time.from_nat 1 + t
  in
  get_state_up_to new_t = voters_round_step new_t (update_votes new_t (get_state_up_to t)).
Proof.
  auto.
Qed.


Lemma voter_state_continuos_existence_step `{io:Io}
  (v:Voter)
  (t: Time)
  (
    is_some_at_t
    : is_some(
        Dictionary.lookup
        v
        (voters_state (get_state_up_to t))
      )=true
  )
    : is_some(
        Dictionary.lookup
        v
        (voters_state (get_state_up_to ((Time.from_nat 1)+t)%natWrapper ))
      ) = true.
Proof.
  destruct t as [t0].
  induction t0.
  - apply voter_state_continuos_existence_step_1.
    auto.
  - rewrite get_state_up_to_unfold.
    apply voter_state_continuos_existence_in_voters_round_step.
    apply voter_state_continuos_existence_in_update_votes.
    auto.
Qed.

Lemma voter_state_continuos_existence `{io:Io}
  (v:Voter)
  (t: Time)
  (
    is_some_at_t
    : is_some(
        Dictionary.lookup
        v
        (voters_state (get_state_up_to t))
      )= true
  )
  (t_increment:Time)
    : is_some(
        Dictionary.lookup
        v
        (voters_state (get_state_up_to (t_increment+t)%natWrapper ))
      ) = true.
Proof.
  destruct t_increment as [n_increment].
  induction n_increment.
  - simpl.
    auto.
  - pose (voter_state_continuos_existence_step v (Time.from_nat n_increment + t)) as H.
    apply H.
    auto.
Qed.

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
