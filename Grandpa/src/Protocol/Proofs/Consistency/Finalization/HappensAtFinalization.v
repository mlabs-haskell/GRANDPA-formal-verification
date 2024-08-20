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

Require Protocol.Proofs.Consistency.old_consistency.

(**
We show that the protocol only alters the global list of finalized blocks
in the message processing stage
  [finalized_blocks_after_round_came_from_finalize_block].
*)


Section OnlyPlaceOfModification.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

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
  destruct (process_round_voters_from (io_get_round_voters (RoundNumber.from_nat 0))) as [[_ prevote_voters_list] precommit_voters_list].
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

End OnlyPlaceOfModification.
