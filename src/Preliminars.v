Require Import Blocks.
Require Import Votes.

(* Función g *)
Definition g {bizantiners_number last_block_number out}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  : option (Block out).
(* TODO: Provide definition *)
Admitted.

(*
  let valid_votes := 
    filter (fun v => match v with 
                     | VoteC _ _ _ _ _ _ => true 
                     | _ => false 
                     end) 
           (projT2 T) in
  let sorted_votes := 
    sort (fun v1 v2 => if leb (projT2 v1) (projT2 v2) then true else false) 
         valid_votes in
  match sorted_votes with
  | [] => OriginBlock
  | h :: _ => projT1 h
  end.
*)


Lemma lemma_2_5_2 {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  (is_safe_t: isSafe T = true)
  (S: Votes voters last_block) 
  (is_sub_set: IsSubset S T )
  {gs_block_number: nat}
  (gs : Block gs_block_number)
  (gs_is_result : g S = Some gs)
  (gt_block_number: nat)
  (gt : Block gt_block_number)
  (gt_is_result : g T = Some gt)
  :Prefix gs gt. 
Admitted.


Variant ImpossibleSupermajority {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  {new_block_number: nat}
  (new_block: Block new_block_number)
  :Prop
  := 
  | ImpossibleByOtherChain {other_block_number:nat} (other_block: Block other_block_number) (*TODO: fill this*) : ImpossibleSupermajority T new_block
  | ImpossibleByEquivocations (*TODO FIll this*) : ImpossibleSupermajority T new_block.


Definition PossibleSupermajority {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  {new_block_number: nat}
  (new_block: Block new_block_number)
  :Prop
  := not (ImpossibleSupermajority T new_block).


Lemma lemma_2_6_1 {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S: Votes voters last_block)
  {block1_number block2_number: nat}
  (block1: Block block1_number)
  (block2: Block block2_number)
  (is_prefix: Prefix block1 block2)
  : ImpossibleSupermajority S block1 -> ImpossibleSupermajority S block2.
Admitted.

Lemma lemma_2_6_2 {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S T: Votes voters last_block)
  {block_number : nat}
  (block: Block block_number)
  : ImpossibleSupermajority S block -> ImpossibleSupermajority T block.
Admitted.

Lemma lemma_2_6_3 {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S: Votes voters last_block)
  {gs_block_number:nat}
  (gs : Block gs_block_number)
  (gs_is_result : g S = Some gs)
  {block_number : nat}
  (block: Block block_number)
  (unrelated_proof: Unrelated block gs)
  : ImpossibleSupermajority S block.
Admitted.

  



(* TODO: Define:

- Time
- Round
- Estimate 

Module preliminars.


Inductive Maybe : Type -> Type :=
 | Just  {T:Type}  (t:T) : Maybe T
 | Nothing  {T:Type}: Maybe T.

Definition SetOfVotes := nat.

Definition checkSuperMajority (S:SetOfVotes) : bool := true.



Definition g (n:SetOfVotes) : Maybe Block := Nothing.



Example SOme : Block = Block .


Inductive Time := | TimeC nat.

Definition Voter := nat.

Definition Voters := list nat.

Definition Vote := list Block.

Inductive Round : Voters-> Time -> nat -> Type := 
  | EmptyRound  (vs:Voters) (t:Time) (round_number:nat) : 
      Round vs t round_number
  | RoundStep {vs:Voters} {t_prev:Time} {round_number:nat}  
    (previous_step:Round vs t_prev round_number)  
    (new_votes:list (Vote * nat) ): 
    Round vs (t_prev +1) round_number
  | NewRound {vs:Voters} {t_prev:Time} {round_number:nat}  
    (previous_round:Round vs t_prev round_number)  
    (new_voters:Voters ): 
    Round new_voters (t_prev +1) (round_number+1).




 *)
