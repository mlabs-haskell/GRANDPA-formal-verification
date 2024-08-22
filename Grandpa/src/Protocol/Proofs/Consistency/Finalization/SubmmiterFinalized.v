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
Require Import Protocol.Io.

Require Import Classes.Functor.
Require Import Classes.Eqb.
Require Import Classes.Math.All.
Require Import Instances.List.

Require Protocol.Proofs.Consistency.VoterStateExists.
Require Protocol.Proofs.Consistency.Rounds.Existence.

(**
  This module focus is to proof that every finalized block
  in the finalization list, was indeed submitted by the
   voter mentioned in the list.
*)


Section SubmitterFinalized.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Theorem finalized_block_was_submitted `{io:Io}
  (fb:FinalizedBlock)
  {t:Time}
  (in_finalization_list: List.In fb (global_finalized_blocks (get_state_up_to t) ))
  :
  let v := fb.(FinalizedBlock.submitter_voter)
  in
  let t := fb.(FinalizedBlock.time)
  in
  let r_n := fb.(FinalizedBlock.round_number)
  in
  let state := update_votes t (get_state_up_to t)
  in
  (exists vs r,
    (get_voter_state v initial_state = Some vs)
    /\
    (Existence.IsRoundAt v t r_n r)
    /\
    (List.In (r,fb.(FinalizedBlock.block)) (get_blocks_to_finalize v vs))
  ).
  (*TODO: critical
    Use the fact that all finalization blocks must happen at the finalization
    function, then show that all blocks can only form a finalization
     if it has their information.
    You may need a lemma subsumming the [state] defined here and
     the real state, as the finalization is run over the a state
     thay may be modified by the finalization of other voters.
    The tricky part is that at every step finalization may add
     finalized blocks to the global list, so, the order of insertion
     matters.
   *)
  Admitted.

(*TODO: Maybe rename GlobalListMonotone module to GlobalList and add this?
*)
Corollary in_finalization_list_means_time_is_at_least `{io:Io}
  (fb:FinalizedBlock)
  {t:Time}
  (in_finalization_list: List.In fb (global_finalized_blocks (get_state_up_to t) ))
  :  fb.(FinalizedBlock.time) < t.
Admitted.

Theorem finalized_block_has_supermajority_at_finalization `{io:Io}
  {t:Time}
  (fb:FinalizedBlock)
  (in_finalization_list: List.In fb (global_finalized_blocks (get_state_up_to t) ))
  :
  let v := fb.(FinalizedBlock.submitter_voter)
  in
  let t := fb.(FinalizedBlock.time)
  in
  let r_n := fb.(FinalizedBlock.round_number)
  in
  let state := update_votes t (get_state_up_to t)
  in
  (exists vs r,
    (get_voter_state v initial_state = Some vs)
    /\
    (Existence.IsRoundAt v t r_n r)
    /\
    Votes.block_has_supermajority fb.(FinalizedBlock.block) (OpaqueRound.get_all_prevote_votes r) = true
  ).
Admitted.


End SubmitterFinalized.
