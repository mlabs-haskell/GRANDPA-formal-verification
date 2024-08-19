Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import State.
Require Import Time.
Require Import RoundNumber.
Require Import Preliminars.
Require Import DataTypes.List.Count.
Require Import DataTypes.List.Fold.
Require Import Protocol.FinalizedBlock.
Require Import Protocol.Io.
Require Import Protocol.Protocol.

Require Import PeanoNat.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Require Protocol.Proofs.Consistency.old_consistency.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Definition VoterVotedInRound (v:Voter) (opaque:OpaqueRound.OpaqueRoundState)
  :Prop
  :=
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_prevote_votes opaque) = true)
    \/
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_precommit_votes opaque) = true).

Definition voter_is_hones_at_round `{Io} (v:Voter) (r:RoundNumber) : bool
  :=
  (0 <? count v (get_round_honest_voters r))%nat.


Lemma voter_round_step_aux_dont_finalize_blocks `{Io}
  (t:Time)
  (state:State)
  (voter:Voter)
  :
  State.global_finalized_blocks state
  =
  State.global_finalized_blocks (voter_round_step_aux t state voter).
Admitted.

Lemma update_votes_dont_finalize_blocks `{Io}
  (t:Time)
  (state:State)
  :
  State.global_finalized_blocks (StateMessages.update_votes t state)
  =
  State.global_finalized_blocks state.
Admitted.

Lemma round_zero_only_finalises_origin_block `{io:Io}
  :
  State.global_finalized_blocks
    (get_state_up_to (Time.from_nat 0))
  =
  (State.global_finalized_blocks initial_state).
Proof.
  unfold get_state_up_to.
  unfold make_initial_state_from.
  destruct (process_round_voters_from (io_get_round_voters (from_nat 0))) as [[_ prevote_voters_list] precommit_voters_list].
  auto.
Qed.

Definition global_finalization_step `{io:Io}
  (t:Time)
  (state:State)
  : State
  :=
  List.fold_left
    (fun new_state info => finalization t new_state (fst info) (snd info))
    (Dictionary.to_list state.(State.voters_state))
    state.

Lemma voter_round_step_finalises `{io:Io}
  (t:Time)
  (state:State)
  (voter:Voter)
  {vs:VoterState.VoterState}
  (has_voter_state: get_voter_state voter state = Some vs)
  :
  global_finalized_blocks (voter_round_step t state voter)
  =
  global_finalized_blocks (finalization t state voter vs)
  .
Proof.
  unfold voter_round_step.
  rewrite has_voter_state.
  rewrite <- voter_round_step_aux_dont_finalize_blocks.
  auto.
Qed.

Lemma fold_voter_step_finalises `{io:Io}
  (t:Time)
  (state:State)
  :
  global_finalized_blocks
    (List.fold_left (voter_round_step t)
       (List.map fst (Dictionary.to_list (voters_state state))) state) =
  global_finalized_blocks
    (List.fold_left
       (fun (new_state : State) (info : Voter * VoterState.VoterState) =>
        finalization t new_state (fst info) (snd info))
       (Dictionary.to_list (voters_state state)) state).
Proof.
  Admitted.

Lemma voters_round_step_finalized_exactly `{io:Io}
  (t:Time)
  (state:State)
  :
  State.global_finalized_blocks (voters_round_step t state)
  =
  State.global_finalized_blocks (global_finalization_step t state).
Proof.
  unfold voters_round_step.
  unfold global_finalization_step.
  simpl.
  apply fold_voter_step_finalises.
Qed.


Lemma finalized_blocks_after_round_came_from_finalize_block_step `{io:Io}
  (t:Time)
  (state:State)
  :
  State.global_finalized_blocks
    (voters_round_step
      t
      (StateMessages.update_votes t state)
    )
  =
  State.global_finalized_blocks (global_finalization_step
    t state).
Proof.
  rewrite <- voters_round_step_finalized_exactly.
  Admitted.

Lemma finalized_blocks_after_round_came_from_finalize_block `{io:Io}
  (t:Time)
  :
  State.global_finalized_blocks (get_state_up_to (Time.from_nat 1+t))
  =
  State.global_finalized_blocks (global_finalization_step
    (Time.from_nat 1+ t) (get_state_up_to t)).
Proof.
  rewrite old_consistency.get_state_up_to_unfold.
  apply finalized_blocks_after_round_came_from_finalize_block_step.
Qed.

Lemma theorem_4_1_eq_aux `{Io}
  (t:Time)
  (fb: FinalizedBlock)
  (b1_in:List.In fb (global_finalized_blocks (get_state_up_to t)))
  :
  exists
  (vr:OpaqueRound.OpaqueRoundState)
  (vr2:OpaqueRound.OpaqueRoundState)
  ,
  let v := fb.(FinalizedBlock.submitter_voter)
  in
    (
      State.get_voter_opaque_round
        (get_state_up_to fb.(FinalizedBlock.time) )
        v
        fb.(FinalizedBlock.round_number)
      =
      Some vr
    )
    /\
    (
      g
        (OpaqueRound.get_all_precommit_votes vr)
      =
      Some fb.(FinalizedBlock.block)
    )
    /\
    (
      State.get_voter_opaque_round
        (get_state_up_to (t+(Time.from_nat 2)*global_time_constant))
        v
        fb.(FinalizedBlock.round_number)
      =
      Some vr2
    ).
Proof.
  Admitted.
  (*
  pose (finalized_block_time_leq b1 round_finalized t1 t b1_in) as t1_leq_t.
  remember (t+(Time.from_nat 2)*global_time_constant) as new_t eqn:new_t_eq.
  assert (List.In (to_any b1,t1, round_finalized) (global_finalized_blocks (get_state_up_to new_t))) as b1_in_new_t.
  {
    pose (finalized_blocks_monotone_over_time2 t (new_t - t) (to_any b1, t1,round_finalized) b1_in).
    enough ((new_t - t +t) = new_t) as H0.
    rewrite <- H0.
    assumption.
    admit.
    (* lia. *)
    }
  destruct (finalized_block_came_from_voter b1 round_finalized t1 new_t  b1_in_new_t) as [v [vr [is_some_vr g_vr]]].
  exists v.
  pose (round_continuos_existence v t1 round_finalized vr is_some_vr (new_t - t1)) as vr_exists_at_new_t.
  assert (new_t - t1 +t1 = new_t) as is_new_t. admit. (* lia. *)
  Admitted.
  *)
  (*
  rewrite is_new_t in vr_exists_at_new_t.
  simpl in vr_exists_at_new_t.
  destruct vr_exists_at_new_t as [vr2 is_some_vr2].
  exists vr.
  exists vr2.
  auto.
Qed.
   *)


Lemma theorem_4_1_eq `{io:Io}
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:
    Unrelated
      fb1.(FinalizedBlock.block).(AnyBlock.block)
      fb2.(FinalizedBlock.block).(AnyBlock.block)
  )
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (finalized_same_round : fb1.(FinalizedBlock.round_number) = fb2.(FinalizedBlock.round_number))
  :
  exists
    (t3:Time)
    (v:Voter)
    (r:OpaqueRound.OpaqueRoundState)
    (s:Sets.DictionarySet Voter)
    ,
    (
      (
        State.get_voter_opaque_round (get_state_up_to t3) v fb1.(FinalizedBlock.round_number) = Some r
      )
      /\
      (
        List.length (Sets.to_list s)
        >=
        1+ Voters.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      )%nat
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters fb1.(FinalizedBlock.round_number) ))
    ).
Proof.
  (*
  remember (t + (Time.from_nat 2) * global_time_constant) as new_t eqn:new_t_eq.
  exists new_t.
  destruct (theorem_4_1_eq_aux b1 round_finalized t1 t b1_in) as [v [v1r [v1r2 [is_some_v1r [g_v1r is_some_v1r2]]]]].
  exists v.
  exists v1r2.
  remember (List.filter (fun v3 => Votes.voter_voted_in_votes v3 (OpaqueRound.get_all_precommit_votes v1r2)) (get_round_bizantine_voters round_finalized)) as s_as_list eqn:s_as_list_eq.
  remember (Sets.from_list s_as_list) as s.
  exists s.
  rewrite <- new_t_eq in is_some_v1r2.
  split.
  assumption.
  split.
  - destruct (theorem_4_1_eq_aux b2 round_finalized t2 t b2_in) as [v2 [v2r [v2r2 [is_some_v2r [g_v2r is_some_v2r2]]]]].
  *)
    (*
       TODO in 3.8 :
       we need to show that after t+2*global_time_constant v has got all the votes on v2r, and as such we have
       a supermajority for both blocks in this round (b1 and b2) at this time.
       Then we destruct the Votes.is_safe predicate applied in the precommits at time t + 2*global_time_constant
       In the False case, we end this sub-proof.
       In the True case, b_1 and b_2 are related by a lemma in the Votes.v about supermajority on safe sets, contra with un_related
    *)
  (*
    The other two parts to be proved, are a consequency of the construction of the list (literally they are in the predicate that build the list).
   *)
    Admitted.



Lemma theorem_4_1_lt `{io:Io}
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:
    Unrelated
      fb1.(FinalizedBlock.block).(AnyBlock.block)
      fb2.(FinalizedBlock.block).(AnyBlock.block)
  )
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (symmetry_hipotesis:
    fb1.(FinalizedBlock.round_number)
    <
    fb2.(FinalizedBlock.round_number)
  )
  :
  exists
    (t3:Time)
    (v:Voter)
    (r_n:RoundNumber)
    (r:OpaqueRound.OpaqueRoundState)
    (s:Sets.DictionarySet Voter)
    ,
    (
      (
        State.get_voter_opaque_round (get_state_up_to t3) v r_n = Some r
      )
      /\
      (
        List.length (Sets.to_list s)
        >=
        1+ Voters.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      )%nat
      /\
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters r_n))
    ).
Proof.
  (*
  dependent induction b1.
  - pose (originBlock_is_always_prefix b2) as contra.
    apply (prefix_implies_related _ _) in contra.
    contradiction.
  - dependent destruction b2.
    +  pose (originBlock_is_always_prefix (NewBlock b1 id)) as contra.
       apply (prefix_implies_related _ _) in contra.
       apply related_symmetric in contra.
       contradiction.
    +
      (*TODO in 3.8 *)
  *)
Admitted.


(** Theorem 4.1
The original lemma states that

  if we finalized two unrelated blocks
  [fb1] y [fb1], then we can find a set [s] of voters such that
     |s| >= 1
  and all of the voters in [s] voted in a particular vote. Even better
  there exists a synchronous way to find such a set.

This doesn't tell anything a bout a synchronous procedure,
but by virtue of coq constructive logic, the proof
of this theorem shows the existence of a procedure to
find the set.

Additionally, we need to state the theorem conclusion in
terms of the particular view of a particular voter at some time.
This, since we don't have a notion of
  " all the votes emitted for a round at a time"
ad
*)
Theorem theorem_4_1 `{io:Io}
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:
    Unrelated
      fb1.(FinalizedBlock.block).(AnyBlock.block)
      fb2.(FinalizedBlock.block).(AnyBlock.block)
  )
  (fb1_in:
    List.In fb1 (global_finalized_blocks (get_state_up_to t))
  )
  (fb2_in:
    List.In fb2 (global_finalized_blocks (get_state_up_to t))
  )
  :
  exists
    (t3:Time)
    (v:Voter)
    (r_n:RoundNumber)
    (r:OpaqueRound.OpaqueRoundState)
    (s:Sets.DictionarySet Voter)
    ,
    (
      ((* Exists a voter [v] that sees the round [r] at time [t3].
          All the rest of the statements reference to the view of
          this particular voter v.
      *)
        State.get_voter_opaque_round (get_state_up_to t3) v r_n = Some r
      )
      /\
      ((* Exists a set [s] with at least [1+f] voters of round [r].*)
        List.length (Sets.to_list s)
        >=
        1+ Voters.calculate_max_bizantiners (OpaqueRound.get_prevote_voters r)
      )%nat
      /\
      (*  All voters of  [s] emitted a vote  in round [r]. *)
      (forall v2, List.In v2 (Sets.to_list s) -> VoterVotedInRound v2 r)
      /\
      (* All voters of [s] are byzantine voters for round [r] *)
      (forall v3, List.In v3 (Sets.to_list s) -> List.In v3 (get_round_bizantine_voters r_n))
    ).
Proof.
  (* Use naturals trichotomy to stablish for [fb1] y [fb2] tree possible cases:
     - fb1 was finalized in a round below fb2
     - fb1 and fb2 where finalized in the same round
     - fb2 was finalized in a round below fb1.
     Name this fact as [trico]
  *)
  pose (
    Arith.Compare_dec.lt_eq_lt_dec
    (RoundNumber.to_nat fb1.(FinalizedBlock.round_number))
    (RoundNumber.to_nat fb2.(FinalizedBlock.round_number))
  ) as trico.
  (* Tell the interpreter we are going to handle the tree cases
     by separate and rename trico according to the hypothesis.
  *)
  destruct trico as [[fb1_n_lt_fb2_n | fb1_n_eq_fb2_n]| fb2_n_lt_fb1_n].
  (*Solve the case fb1 finalized in a round below fb2, by using lemma
     [theorem_4_1_lt] for it.
  *)
  - apply (
      theorem_4_1_lt
        t
        fb1
        fb2
        un_related
        fb1_in
        fb2_in
        fb1_n_lt_fb2_n
    );try assumption.
  (* Focus on case for fb1 and fb2 finalized in the same round.*)
  -
    (* Convince coq that we can apply our auxiliar theorem here*)
    assert( fb1.(round_number) = fb2.(round_number) ) as fb1_n_eq_fb2_n_2. {
      destruct (fb1.(round_number)).
      destruct (fb2.(round_number)).
      auto.
    }
    (* Applying [theorem_4_1_eq] for this case*)
    destruct (
      theorem_4_1_eq
        t
        fb1
        fb2
        un_related
        fb1_in
        fb2_in
        fb1_n_eq_fb2_n_2
    ) as [t3 [v3 [ r [s result]]]].
    exists t3.
    exists v3.
    exists (fb1.(FinalizedBlock.round_number)).
    exists r.
    exists s.
    assumption.
    (*Focus case fb2 was finalized in a round below fb1 *)
  -
    (*Telling coq that the fact that two blocks are unrelated is symmetric*)
    pose (
      Blocks.Block.unrelated_symmetric
        fb1.(block).(AnyBlock.block)
        fb2.(block).(AnyBlock.block)
        un_related
    ) as un_related2.
    (*Solving this case by using theorem_4_1_lt*)
    apply (
      theorem_4_1_lt
      t
      fb2
      fb1
      un_related2
      fb2_in
      fb1_in
    );try assumption.
Qed.


Corollary corollary_4_3
  `{Io}
  (round_finalized_number:RoundNumber)
  (time_finalied:Time)
  (b_finalized:AnyBlock)
  (v:Voter)
  (r_n:RoundNumber)
  (is_honest: voter_is_hones_at_round v r_n = true)
  (t_increment:Time)
  (r_n_geq: r_n >= round_finalized_number)
  (opaque_r_n : OpaqueRound.OpaqueRoundState)
  (opaque_from_state
    :
    State.get_voter_opaque_round (get_state_up_to (t_increment + time_finalied) ) v r_n
    = Some opaque_r_n
  )
  (r_n_completable:
   OpaqueRound.is_completable opaque_r_n = true
  )
  :exists (eb:AnyBlock),
    (
      OpaqueRound.get_estimate opaque_r_n
      =
      Some eb
    )
    /\
    (
      Block.is_prefix b_finalized.(AnyBlock.block) eb.(AnyBlock.block) = true
    ).
Proof.
  (*TODO: delayed until 3.8
   *)
  Admitted.

Close Scope bool.
Close Scope list.
Close Scope eqb.
Close Scope math.
Close Scope natWrapper.
