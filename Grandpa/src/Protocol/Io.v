Require Import Blocks.AnyBlock.
Require Import Time.
Require Import Voter.
Require Import Message.
Require Import RoundNumber.
Require Import VoterState.

Require Import Classes.Functor.
Require Import Instances.List.

Require Import Classes.Eqb.

(** *Io
The Io class help us abstract the external world.

Every instance of Io allow us to change the details of the model.

By example, we can create a Io that help us model the fact that
all participant are byzantine voters or none of them are. Or we can
model a completely synchronous network.

In particular we store:
  - The GST constant
  - A bound T constant that guarantees communication between participants
  - A [block_producer] function returning all the blocks for which a participant
    can vote in a round.
  - A [accept_vote] function that allow us to model when a vote is received
   (is harcoded in the protocol the fact that after GST + 2T the message should be
    received).
  - A [bizantine_vote] function representing when and for what block a byzantiner
    will vote.
  - A [bizantine_advance_round] functions representing the time at witch a
    byzantiner voter should advance to the next round.
  - A [get_round_voters] functions that tell us who are the voters of a round
    and for every one of the voters of that round it also tell us if the
    voter is byzantine and if it is a prevoter or precommiter.
  - A [get_round_primary] to choose for us a primary for a round.
  - Additional predicates about well behaviour of the functions in Io.

*)

Class Io := {
  globa_synchrony_time:Time;
  global_time_constant: Time;
  block_producer (time: Time) (voter:Voter) :
    Sets.DictionarySet AnyBlock;
  io_accept_vote : Time -> Message -> Voter -> bool;
  (*TODO: add a constraint to make io_bizantine_vote return nothing after io_bizantine_advance_round is true*)
  io_bizantine_vote : Time -> Voter -> option AnyBlock;
  (*TODO: add a constraint to make io_bizantine_advance_round true after the first time it returns true for a round*)
  io_bizantine_advance_round : Time -> Voter-> RoundNumber -> bool;
  io_get_round_voters:  RoundNumber -> Dictionary.Dictionary Voter VoterKind;
  io_get_round_primary : RoundNumber -> Voter;
  (*TODO: add more restrictions to the block producer:
     - If v1 sees block b at t1 then all other v see b at t1+T
- if v sees block b at t1, then
         v sees b at t1+ t2 forall t2
  *)
  block_producer_not_emtpy
    :forall t v, Sets.is_empty (block_producer t v) = false;
    primary_consistent
      : forall r ,
          List.In
            (io_get_round_primary r)
            (
              map fst (Dictionary.to_list (io_get_round_voters r ))
            );

  all_voters_are_in_0_round : forall voter r, (exists (kind:VoterKind),
    Dictionary.lookup voter (io_get_round_voters r) = Some kind )->
      exists (kind0:VoterKind),
        Dictionary.lookup voter (io_get_round_voters (RoundNumber.from_nat 0))
        = Some kind0;

  minimum_voters_per_round :
    forall rn, 5 <= List.length (Dictionary.to_list (io_get_round_voters (RoundNumber.from_nat rn)));
}.

Definition get_all_time_participants `{Io} : list Voter
  :=
  map fst (Dictionary.to_list (io_get_round_voters (RoundNumber.from_nat 0))).

Definition voter_is_primary_for_round `{Io} (v:Voter) (round_number:RoundNumber):bool
  :=
  io_get_round_primary round_number =? v.

Definition get_round_bizantine_voters `{Io} (round_number:RoundNumber)
  :list Voter
  :=
  let f v_k :=
    match v_k with
    | (_,VoterKindC Bizantine _) => true
    | _ => false
    end
  in
  map fst  (List.filter f (Dictionary.to_list (io_get_round_voters round_number)) ).

Definition get_round_honest_voters `{Io} (round_number:RoundNumber)
  :list Voter
  :=
  let f v_k :=
    match v_k with
    | (_,VoterKindC Honest _) => true
    | _ => false
    end
  in
  map fst  (List.filter f (Dictionary.to_list (io_get_round_voters round_number)) ).

Close Scope list.
