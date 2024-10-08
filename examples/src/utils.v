From Grandpa.Blocks Require Import Block.
From Grandpa Require Import Votes.

Open Scope list.


Fixpoint make_block_aux (ids:list nat) : Block (List.length ids)
  :=
  match ids return Block (List.length ids) with
  | nil => OriginBlock
  | id :: remain => 
      NewBlock (make_block_aux remain) id
  end.


Definition make_block (ids:list nat) : Block (List.length ( List.rev ids))
  :=
  make_block_aux (List.rev ids). 

(*Definition make_voters (bizantiners_number:nat) (last_block_number:nat)
  (block:last_block_number)
  (ls:list (nat*(list nat)))
  : Voters bizantiners_number

Definition make_votes (bizantiners_number:nat) (list (nat*(list nat)))
  : Votes 
*)

Close Scope list.
