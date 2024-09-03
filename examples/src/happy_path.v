From Grandpa Require Import Blocks.Block.
From Grandpa Require Import Vote.
From Grandpa Require Import Votes.
From Grandpa Require Import Voters.
From Grandpa Require Import Classes.Functor.

Example e_block1 := NewBlock OriginBlock 10.
Example e_block2 := NewBlock OriginBlock 10.
Example e_block3 := NewBlock OriginBlock 12.
Example e_block4 := NewBlock OriginBlock 10.
Example e_block5 := NewBlock OriginBlock 10.
Example e_block6 := NewBlock OriginBlock 10.
Example e_block7 := NewBlock (NewBlock OriginBlock 10) 22.
Example e_block8 := NewBlock (NewBlock OriginBlock 11) 22.
Example e_block9 := NewBlock (NewBlock OriginBlock 10) 23.

Open Scope list.
Example e_voters_list := (1::2::3::4::5::6::7::8::9::List.nil).

Example e_voters: Voters 
  := 
  Voters.from_list 
    (map Voter.from_nat e_voters_list)
    (List.length e_voters_list).

Example false_in x : Voters.In x e_voters.
Admitted.

Definition mk {m:nat} (n:nat) (b: Block m) 
  : Vote e_voters
  := 
  {| 
    Vote.block_number:=m
    ;Vote.block:=b
    ;Vote.voter:=Voter.from_nat n
    ;Vote.in_voters:=false_in (Voter.from_nat n)
  |}.

Example votes_list := 
  (
  mk 1 e_block1
  :: mk 2 e_block2
  ::mk 3 e_block3
  ::mk 4 e_block4
  ::mk 5 e_block5
  ::mk 6 e_block6
  ::mk 7 e_block7
  ::mk 8 e_block8
  ::mk 9 e_block9
  :: List.nil
  ).

Example e_votes := VotesC e_voters votes_list.

Compute split_voters_by_equivocation e_votes .
Compute count_votes e_votes.
Compute Voters.length e_voters.
Compute get_supermajority_blocks e_votes .


Example test1 : 
  get_supermajority_blocks e_votes 
    = List.cons (AnyBlock.to_any (NewBlock OriginBlock 10), 7) List.nil.
Proof.
  reflexivity.
Qed.

Close Scope list.
