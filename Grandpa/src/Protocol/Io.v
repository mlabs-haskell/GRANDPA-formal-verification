Require Import Blocks.AnyBlock.
Require Import Time.
Require Import Voter.
Require Import Message.
Require Import RoundNumber.
Require Import VoterState.

Require Import Classes.Functor.
Require Import Instances.List.

Require Import Classes.Eqb.


Class Io := {
  global_time_constant: Time;
  block_producer (time: Time) (voter:Voter) : 
    Sets.DictionarySet AnyBlock;
  io_accept_vote : Time -> Message -> Voter -> bool;
  (* the nat is the round number*)
  io_bizantine_vote : Time -> Voter -> option AnyBlock;
  io_bizantine_advance_round : Time -> Voter-> RoundNumber -> bool;
  io_get_round_voters:  RoundNumber -> Dictionary.Dictionary Voter VoterKind;
  (*TODO: add an Io that returns all time participants and use in initialization*)
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
        (map fst (Dictionary.to_list (io_get_round_voters r )));
}.

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
