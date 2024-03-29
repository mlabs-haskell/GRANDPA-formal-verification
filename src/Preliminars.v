Require Import Blocks.
Require Import Votes.
Require List.
Require Import Nat.

(* Función g *)
Definition g {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  : option (sigT ( fun out => Block out))
  := 
  let (equivocate_voters, non_equivocate_voters) 
    := split_voters_by_equivocation T
  in
  let number_of_equivocates := length equivocate_voters
  in
  let count  
    := 
    count_votes  
      (filter_votes_by_voters_subset 
        voters 
        last_block 
        T 
        (VotersC bizantiners_number non_equivocate_voters)
      )
  in
  let has_supermajority_predicate block_and_vote := 
    match block_and_vote with
    | (_, number_of_votes) 
        => 
        voters_length voters + bizantiners_number +1 
        <? 2 * (number_of_votes + number_of_equivocates)
    end
  in
  let blocks_with_super_majority 
    := 
    List.filter has_supermajority_predicate 
      (BlockDictionaryModule.to_list count)
  in
  let join (existencial:AnyBlock) acc 
    := 
    match existencial with
    | existT _ block_number block =>
        match acc with
        | List.nil => List.cons existencial List.nil
        | List.cons h others 
            => match h with 
               | existT _ h_block_number _ =>
                   if h_block_number <? block_number 
                   then List.cons existencial List.nil
                   else 
                    if Nat.eqb h_block_number  block_number 
                    then List.cons existencial acc
                    else
                      acc
              end
        end
    end
  in
  match   
    List.fold_right join List.nil (List.map fst blocks_with_super_majority) 
  with
    | List.cons result List.nil => Some result
    | _ => None
  end.


Lemma lemma_2_5_2 {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  (is_safe_t: is_safe T = true)
  (S: Votes voters last_block) 
  (is_sub_set: IsSubset S T )
  {gs_block_number: nat}
  (gs : Block gs_block_number)
  (gs_is_result : g S = Some (existT _ gs_block_number gs))
  (gt_block_number: nat)
  (gt : Block gt_block_number)
  (gt_is_result : g T = Some (existT _ gt_block_number  gt))
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
  (gs_is_result : g S = Some (existT _ gs_block_number gs))
  {block_number : nat}
  (block: Block block_number)
  (unrelated_proof: Unrelated block gs)
  : ImpossibleSupermajority S block.
Admitted.
