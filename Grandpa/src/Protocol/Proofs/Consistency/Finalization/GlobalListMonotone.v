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

(**
   We proof that the global list of finalized blocks grows
   over time (is monotone).

   Main result : [finalized_blocks_list_is_monotone]
*)


Section IsMonotone.

Open Scope bool.
Open Scope list.
Open Scope eqb.
Open Scope math.
Open Scope natWrapper.

Definition finalized_blocks_list_is_monotone : Type.
(*TODO: Define and proof*)
Admitted.


End IsMonotone.
