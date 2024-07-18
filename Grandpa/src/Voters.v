Require Import PeanoNat.

Require Import DataTypes.Sets.
Require Import Instances.Nat.
Require Import Classes.Eqb.
Require Import Classes.Functor.
Require Import Instances.List.
Require Import DataTypes.List.Count.

Require Import Voter.

(** * Voters
*)


Record Voters : Type 
  := VotersC {to_set: DictionarySet Voter
      ;round_number_of_voters: nat
  }.

Definition to_list (voters:Voters)
  : list Voter
  := Sets.to_list (to_set voters).

Definition length (voters:Voters)
  := 
  length (to_list voters).

Definition from_list (voters:list Voter) 
  (round_number_of_voters:nat)
  : Voters
  := {| to_set:= Sets.from_list voters
        ;round_number_of_voters:=round_number_of_voters
    |}.

(*
Definition voters_voters_and_list 
  (voters:Voters)
  (ls:list Voter)
  : Voters 
  :=
  from_list ls voters.(round_number_of_voters) .
*)



Definition In
  (voter : Voter) 
  (voters:Voters) 
  :=
  List.In voter (to_list voters).

Definition inb  
  (voter : Voter) (voters:Voters) 
  := 0 <? (count voter (to_list voters)).

Definition calculate_max_bizantiners
  (voters:Voters)
  :nat
  :=
  let total:= voters.(round_number_of_voters)
  in
  match Nat.modulo total 3 with 
  | 0 => (total/3) -1
  | _ => total/3
  end
  .

