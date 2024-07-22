Require Import Blocks.Block.
Require Import Blocks.AnyBlock.
Require Import Voter.
Require Import Voters.

Export Voter.
Export Voters.

Require Import Classes.Eqb.
Require Instances.Tuple.
Require Instances.Nat.


(** Vote

From the paper:

<<
  A vote is a block hash, together with some metadata such as round number 
  and the type of vote, such as prevote or precommit, all signed with a 
  voter’s private key
>>
  
Following the same approach as with the Blocks, we choose to replace the 
block hash with the real block. This makes proofs easier.

Round number would be added later when we add Time and Rounds, this 
  simplifies the work with a Vote.

We don't have types for votes, instead when needed, we distinguish
them by maintaining two different set of votes, one for precommits 
and other for prevotes.

However, we want to tie a Vote with a particular set of Voters 
and to ensure that the Vote is coherent.
*)

Record Vote
  (voters: Voters)
  :Type 
  := 
  VoteC
  {
    block_number:nat 
    ;block: Block block_number
    ;voter : Voter 
    ;in_voters: Voters.In voter voters
  }.


Arguments block_number {voters} .
Arguments block {voters} .
Arguments voter {voters} .
Arguments in_voters {voters} .


Definition to_anyblock
  {voters: Voters }
  (vote: Vote voters )
  : AnyBlock
  :=
  AnyBlock.to_any vote.(block).

Definition to_tuple
  {voters: Voters}
  (vote:Vote voters)
  : Voter * AnyBlock 
  :=
  (vote.(voter), to_anyblock vote).

Section Instances.

Open Scope eqb_scope.

Definition vote_eqb 
  {voters: Voters}
  (vote1 vote2: Vote voters)
  : bool
  :=
    to_tuple vote1 =? to_tuple vote2.

Instance EqbVote (voters:Voters): Eqb (Vote voters) :=
{
  eqb := vote_eqb
}.

Global Existing Instance EqbVote.


#[refine]Instance EqbLawsVote (voters:Voters) : EqbLaws (Vote voters) :=
{
}.
Proof.
  - intro x.
    simpl.
    unfold vote_eqb.
    unfold to_tuple.
    apply eqb_reflexivity.
  - simpl.
    unfold vote_eqb.
    unfold to_tuple.
    intros x y.
    apply eqb_symmetry.
  - intros x y z.
    simpl.
    unfold vote_eqb.
    apply eqb_transitivity.
Qed.

End Instances.
