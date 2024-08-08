Require Import Blocks.AnyBlock.
Require Import Votes.
Require Import State.
Require Import Time.
Require Import RoundNumber.
Require Import Preliminars.
Require Import DataTypes.List.Count.
Require Import Protocol.FinalizedBlock.
Require Import Protocol.Io.
Require Import Protocol.Protocol.

Require Import PeanoNat.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Lemma get_global_finalized_blocks_are_related (state:State)
  (b1 b2 : AnyBlock) 
  (b1_in 
    : List.In b1 (List.map (FinalizedBlock.block) state.(global_finalized_blocks)))
  (b2_in 
    : List.In b2 (List.map (FinalizedBlock.block) state.(global_finalized_blocks)))
  : Related b1.(AnyBlock.block) b2.(AnyBlock.block).
Admitted.


Definition VoterVotedInRound (v:Voter) (opaque:OpaqueRound.OpaqueRoundState)
  :Prop
  :=
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_prevote_votes opaque) = true)
    \/
    (Votes.voter_voted_in_votes v (OpaqueRound.get_all_precommit_votes opaque) = true).

Lemma theorem_4_1_eq_aux `{Io} 
  (t:Time)
  (fb: FinalizedBlock)
  (b1_in:List.In fb (global_finalized_blocks (get_state_up_to t)))
  : exists (v:Voter) (vr:OpaqueRound.OpaqueRoundState) (vr2:OpaqueRound.OpaqueRoundState)
  ,
    (
      State.get_voter_opaque_round (get_state_up_to fb.(FinalizedBlock.time) ) v fb.(FinalizedBlock.round_number)
      =
      Some vr
    )
    /\
    (g (OpaqueRound.get_all_precommit_votes vr) = Some fb.(FinalizedBlock.block))
    /\
    (
      State.get_voter_opaque_round (get_state_up_to (t+(Time.from_nat 2)*global_time_constant)) v fb.(FinalizedBlock.round_number)
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


Lemma theorem_4_1_eq `{Io} 
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:Unrelated fb1.(FinalizedBlock.block).(AnyBlock.block) fb2.(FinalizedBlock.block).(AnyBlock.block))
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (finalized_same_round : fb1.(FinalizedBlock.round_number) = fb2.(FinalizedBlock.round_number))
  : exists (t3:Time) (v:Voter) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
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
  


Lemma theorem_4_1_lt `{Io} 
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:Unrelated fb1.(FinalizedBlock.block).(AnyBlock.block) fb2.(FinalizedBlock.block).(AnyBlock.block))
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  (symmetry_hipotesis: fb1.(FinalizedBlock.round_number) < fb2.(FinalizedBlock.round_number))
  : exists (t3:Time) (v:Voter) (r_n:RoundNumber) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
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


Theorem theorem_4_1 `{Io} 
  (t:Time)
  (fb1 fb2 : FinalizedBlock)
  (un_related:Unrelated fb1.(FinalizedBlock.block).(AnyBlock.block) fb2.(FinalizedBlock.block).(AnyBlock.block))
  (fb1_in:List.In fb1 (global_finalized_blocks (get_state_up_to t)))
  (fb2_in:List.In fb2 (global_finalized_blocks (get_state_up_to t)))
  : exists (t3:Time) (v:Voter) (r_n:RoundNumber) (r:OpaqueRound.OpaqueRoundState) (s:Sets.DictionarySet Voter), 
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
  Admitted.

    (*
  pose (Arith.Compare_dec.lt_eq_lt_dec (RoundNumber.to_nat round_finalized_1) (RoundNumber.to_nat round_finalized_2) ) as trico.
  destruct trico as [[trico4 | trico2]| trico3].
  - apply (theorem_4_1_lt b1 b2 round_finalized_1 round_finalized_2 t1 t2 un_related state t state_is_from_protocol b1_in b2_in);try assumption.  
  - rewrite state_is_from_protocol in b1_in.
    rewrite state_is_from_protocol in b2_in.
    Admitted.
    rewrite <- trico2 in b2_in.
    destruct (theorem_4_1_eq b1 b2 round_finalized_1 t1 t2 un_related  t b1_in b2_in) as [t3 [v3 [r [s remain]]]].
    exists t3.
    exists v3.
    exists round_finalized_1. 
    exists r.
    exists s.
    assumption.
  - pose (Blocks.unrelated_symmetric b1 b2 un_related) as un_related2.
    apply (theorem_4_1_lt b2 b1 round_finalized_2 round_finalized_1 t2 t1 un_related2 state t state_is_from_protocol b2_in b1_in);try assumption.  
Qed.
     *)


Definition voter_is_hones_at_round `{Io} (v:Voter) (r:RoundNumber) : bool
  := 
  (0 <? count v (get_round_honest_voters r))%nat.


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

