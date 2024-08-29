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

(* we use dependent induction*)
Require Import Coq.Program.Equality.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Require Import Lia.

Definition VoterVotedInRound (v:Voter) (opaque:OpaqueRound.OpaqueRoundState)
:Prop
  :=
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_prevote_votes opaque) = true)
   \/
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_precommit_votes opaque) = true).

Definition voter_is_hones_at_round `{Io} (v:Voter) (r:RoundNumber) : bool
:=
  (0 <? count v (get_round_honest_voters r))%nat.

Lemma time_decomposition (t1 t2:Time) (leq_proof:t1 <= t2)
  :(t2 = t1 + (t2 - t1)).
Proof.
destruct t1 as [nt1] eqn:t1_eq.
destruct t2 as [nt2] eqn:t2_eq.
simpl.
simpl in leq_proof.
enough (nt2 = nt1 + (nt2 - nt1))%nat as H .
rewrite <- H at 1. auto.
apply Arith_base.le_plus_minus_stt.
assumption.
Qed.


Lemma theorem_4_1_eq_aux `{io:Io}
  {t:Time}
  (fb: FinalizedBlock)
  (fb_in:List.In fb (global_finalized_blocks (get_state_up_to t)))
  :
  let v := fb.(FinalizedBlock.submitter_voter)
  in
  let r_n := fb.(FinalizedBlock.round_number)
  in
  VoterStateExists.IsParticipant v
  /\
  forall t_increment:Time,
    exists r,
    (Existence.IsRoundAt v (t+t_increment) r_n r)
  .
Proof.
  remember fb.(FinalizedBlock.submitter_voter) as v.
  remember fb.(FinalizedBlock.round_number) as r_n.
  pose (SubmmiterFinalized.finalized_block_was_submitted fb fb_in) as was_finalized.
  destruct was_finalized as [ vs_initial [ r_finalization (vs_is_participant & r_is_at_t1 & in_finalization_list)  ] ].
  (*Proof that [fb1.submitter_voter] has a voter state at the
      at any time.
  *)
  assert (forall t, exists vs, get_voter_state v (get_state_up_to t) = Some vs) as has_vs.
  {
    eapply VoterStateExists.participants_has_voter_state_always.
    unfold VoterStateExists.IsParticipant.
    exists vs_initial.
    subst v.
    assumption.
  }

  (* Specialize the previous lemma to time 0.*)
  assert (VoterStateExists.IsParticipant v) as has_vs_at_init.
  {
    subst v.
    unfold VoterStateExists.IsParticipant.
    eauto.
  }

  split. assumption.

  intros t_increment.
  remember (t + t_increment) as new_t eqn:new_t_eq.
  (*
    We have a lemma that allow us to conclude the existence of the round
     that we want but we need to show first that  fb.time < t .
  *)
  rewrite new_t_eq.
  apply (Rounds.Existence.continuous_existence has_vs_at_init t t_increment r_n).
  assert ( t = fb.(FinalizedBlock.time) + (t - fb.(FinalizedBlock.time))) as H.
  {
    apply time_decomposition.
    destruct (time fb) eqn:fbt_eq.
    pose (Finalization.SubmmiterFinalized.in_finalization_list_means_time_is_at_least _ fb_in) as H.
    destruct t.
    rewrite fbt_eq in H.
    simpl in H.
    simpl.
    lia.
  }
  rewrite H.
  eapply (Rounds.Existence.continuous_existence has_vs_at_init fb.(FinalizedBlock.time) (t-fb.(FinalizedBlock.time)) r_n ).
  subst v r_n.
  eauto.
Qed.




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
    ,
    (
      Rounds.Existence.IsRoundAt v t3 fb1.(FinalizedBlock.round_number) r
      /\
      Votes.is_safe (OpaqueRound.get_all_prevote_votes r) = false
    ).
Proof.
  (**
    We are going to prove that the voter who finalized the  block [fb1]
     at t + synchronisation can see block [fb2] as finalized and has enough
     information to find the set of byzantine voters.
    Why t+synchronisation time?
    To have [fb1] and [fb2] as finalized blocks, we
      must have that [t > max(fb1.time,fb2.time) ]
    So, after synchronisation time we guaranteed that the voter who finalized
     [fb1] can see the finalization information of [fb2].
    We can state this in the lemma explicitly, but is easier to apply it
     in the main theorem if leave it as `exists t3` instead.

  *)
  remember ((Time.from_nat 2) * global_time_constant : Time) as t_increment.
  remember (t + t_increment) as new_t eqn:new_t_eq.
  exists new_t.
  remember fb1.(FinalizedBlock.submitter_voter) as v.
  remember fb1.(FinalizedBlock.round_number) as r_n.
  exists v.
  pose (theorem_4_1_eq_aux fb1 fb1_in) as temp.
  destruct temp as [vs_is_participant exists_round_after_t].
  pose (exists_round_after_t t_increment) as exists_round_at_new_t.
  destruct exists_round_at_new_t as [r r_at_new_t].
  exists r.

  assert (
    t + t_increment
    =
    fb1.(FinalizedBlock.time) + ((t+t_increment) - fb1.(FinalizedBlock.time))
  ) as new_t_eq_t_finalization.
  {
    apply time_decomposition.
    destruct (fb1.(FinalizedBlock.time)) eqn:fbt_eq.
    pose (
      Finalization.SubmmiterFinalized.in_finalization_list_means_time_is_at_least
        _
        fb1_in
    ) as H.
    rewrite fbt_eq in H.
    destruct t.
    simpl.
    simpl in H.
    lia.
  }

  destruct (SubmmiterFinalized.finalized_block_was_submitted fb1 fb1_in)
    as [_ [r_finalization [ _ [ r_at_finalization _ ] ]]].


  rewrite new_t_eq_t_finalization in r_at_new_t.
  pose (
    Rounds.Continuous.rounds_are_updates
      vs_is_participant
      r_finalization
      r
      r_at_finalization
      r_at_new_t
  ) as r_is_update.


  destruct (
    SubmmiterFinalized.finalized_block_has_supermajority_at_finalization
      _
      fb1_in
  )
    as [vs_finalization2 [ r_finalization2 (
        vs2_is_state
        &
        r2_at_finalization
        &
        fb1_has_supermajority_at_fbt
    )]].
  assert (r_finalization2 = r_finalization).
  {
    unfold Existence.IsRoundAt in r_at_finalization.
    unfold Existence.IsRoundAt in r2_at_finalization.
    clear r_is_update.
    rewrite r2_at_finalization in r_at_finalization.
    inversion r_at_finalization.
    auto.
  }
  subst r_finalization2.
  clear r2_at_finalization.
  clear vs2_is_state.
  clear vs_finalization2.

  pose (
    Rounds.Supermajority.supermajority_consistence
    vs_is_participant
    r_at_finalization
    r_at_new_t
    fb1_has_supermajority_at_fbt
  ) as fb1_has_supermajority_at_newt.

  (* Until here, we have a proof that at time t + synchronisation, we have a
     valid round state for the round that finalized fb1 and that fb1
     indeed has supermajority in this round.
  *)
  assert (
    Votes.block_has_supermajority
      fb2.(FinalizedBlock.block)
      (OpaqueRound.get_all_prevote_votes r)
    =
    true
  ) as fb2_has_supermajority_at_new_t.
  {
    pose (
      VotersVerify.all_voters_verify_finalization_eventually
        fb2
        fb1.(FinalizedBlock.submitter_voter)
        vs_is_participant
        (
          fb1.(FinalizedBlock.time)
          + (
            (t + t_increment) - fb1.(FinalizedBlock.time)
          )
        )
    ) as H .

    destruct H as [r3 (r3_at_new_t & r3_has_super_majority)].
    - destruct fb2.(FinalizedBlock.time) as [nt_fb2] eqn:Hfb2.
      pose (
        Finalization.SubmmiterFinalized.in_finalization_list_means_time_is_at_least
          _
          fb2_in
      ) as H.
      rewrite Hfb2 in H.

      destruct fb1.(FinalizedBlock.time) as [nt_fb1].
      subst t_increment.
      destruct global_time_constant as [nt_global].
      destruct t as [nt].
      simpl.
      simpl in H.
      lia.
    - enough (
        r = r3
      ) as H.
      {
        rewrite H.
        auto.
      }
      unfold Existence.IsRoundAt in r_at_new_t.
      simpl in r_at_new_t.
      simpl in r3_at_new_t.
      rewrite <- finalized_same_round in r3_at_new_t.
      subst r_n.
      rewrite r_at_new_t in r3_at_new_t.
      injection r3_at_new_t.
      auto.
  }

  destruct (Votes.is_safe (OpaqueRound.get_all_prevote_votes r)) eqn:His_safe.
  - (* This is false, we have that the blocks are related
       but they aren't!
    *)
    exfalso.
    apply un_related.
    apply (
      Votes.blocks_that_has_supermajority_are_related
        fb1.(FinalizedBlock.block)
        fb2.(FinalizedBlock.block)
        (OpaqueRound.get_all_prevote_votes r)
        His_safe
    ).

  - split.
    + rewrite new_t_eq.
      rewrite new_t_eq_t_finalization.
      simpl.
      subst r_n.
      subst v.
      auto.
    + auto.
Qed.

Lemma theorem_4_1_step `{io:Io}
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:
    Unrelated
      fb1.(FinalizedBlock.block).(AnyBlock.block)
      fb2.(FinalizedBlock.block).(AnyBlock.block)
  )
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (step_hipotesis:
    RoundNumber.from_nat 1
    =
    fb2.(FinalizedBlock.round_number)
    -
    fb1.(FinalizedBlock.round_number)
  )
  :
  exists
    (t3:Time)
    (v:Voter)
    (r_n:RoundNumber)
    (r:OpaqueRound.OpaqueRoundState)
    ,
    (
      Rounds.Existence.IsRoundAt v t3 r_n r
      /\(
          (
          fb1.(FinalizedBlock.round_number)
          <= r_n
          )
          /\
          (
          r_n
          <=fb2.(FinalizedBlock.round_number)
          )
        )
      /\
      Votes.is_safe (OpaqueRound.get_all_prevote_votes r) = false
    ).
Admitted.

Lemma theorem_4_1_lt `{io:Io}
  (t:Time)
  (fb1 : FinalizedBlock)
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  :
  forall n fb2,
    n = RoundNumber.to_nat (fb2.(FinalizedBlock.round_number) - fb1.(FinalizedBlock.round_number))
    ->
    Unrelated
      fb1.(FinalizedBlock.block).(AnyBlock.block)
      fb2.(FinalizedBlock.block).(AnyBlock.block)
    ->
    List.In fb2 (global_finalized_blocks (get_state_up_to t))
    ->
    (
      fb1.(FinalizedBlock.round_number)
      <
      fb2.(FinalizedBlock.round_number)
    )
    ->
  (
  exists
    (t3:Time)
    (v:Voter)
    (r_n:RoundNumber)
    (r:OpaqueRound.OpaqueRoundState)
    ,
    (
      Rounds.Existence.IsRoundAt v t3 r_n r
      /\(
          (
          fb1.(FinalizedBlock.round_number)
          <= r_n
          )
          /\
          (
          r_n
          <=fb2.(FinalizedBlock.round_number)
          )
        )
      /\
      Votes.is_safe (OpaqueRound.get_all_prevote_votes r) = false
    )
  ).
Proof.
  (*
  destruct (
    fb1
  ) as [
    b1 t1 rn1 v1 voters1 precommits1
  ].
  destruct (
    fb2
  ) as [
    b2 t2 rn2 v2 voters2 precommits2
  ].
  simpl in un_related.
  simpl in symmetry_hipotesis.
   *)
  dependent induction n.
  - destruct fb1.(FinalizedBlock.round_number) as [n1].
    intros fb2 h  unrelated fb2_in symmetry_hipotesis.
    destruct fb2.(FinalizedBlock.round_number) as [n2].
    simpl in *.
    exfalso.
    lia.
  - intros fb2 h  unrelated fb2_in symmetry_hipotesis.
    apply (theorem_4_1_step t). try assumption.
    simpl in * .

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
But from this theorem and the fact that all voters synchronize eventually
we can conclude that this result happens for any voter
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
    ,
    (
      Rounds.Existence.IsRoundAt v t3 r_n r
      /\
      Votes.is_safe (OpaqueRound.get_all_prevote_votes r) = false
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
  Admitted.
  (*
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
    split;assumption.
    (*Focus case fb2 was finalized in a round below fb1 *)
  -
    (*Telling coq the fact that two blocks are unrelated is symmetric*)
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
    ). assumption.
Qed.
   *)

Corollary corollary_4_3
  `{Io}
  (fb:FinalizedBlock)
  (fb_in:
  List.In fb (global_finalized_blocks (get_state_up_to (Time.from_nat 1 + fb.(FinalizedBlock.time))))
  )
  :
  forall n v nt,
  let t := (Time.from_nat nt + fb.(FinalizedBlock.time))
  in
  let rn := (RoundNumber.from_nat n +fb.(FinalizedBlock.round_number))
  in
  voter_is_hones_at_round v rn = true
  ->
    (*TODO: complete this, it must say that forall voters the byzantine number should be lower than the max cuota for a safe set*)
  (forall rm, fb.(FinalizedBlock.round_number) <= rm -> rm <= rn -> forall v2, is_safe )
  exists r,
    get_voter_opaque_round (get_state_up_to t) v rn  = Some r
    /\
    (
      OpaqueRound.is_completable r = true
      -> exists eb,
          (
            OpaqueRound.get_estimate r = Some eb
            /\
            Related eb.(AnyBlock.block) fb.(FinalizedBlock.block).(AnyBlock.block)
          )
    )
  .
Proof.
  dependent induction n.
  2:{
  (*TODO: delayed
   *)
  Admitted.

Close Scope bool.
Close Scope list.
Close Scope eqb.
Close Scope math.
Close Scope natWrapper.
