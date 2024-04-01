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
  let blocks_with_super_majority 
    := get_supermajority_blocks T
  in
  (*
    We will look for a block of maximum block_number 
    such that it has supermajority.
    This join help us get a list with the blocks with 
     the maximum length.
   *)
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


Lemma gt_some_implies_supermajority_not_empty {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  {gt_block_number: nat}
  (gt : Block gt_block_number)
  (gt_is_result : g T = Some (existT _ gt_block_number gt))
  : get_supermajority_blocks T <> List.nil.
Proof.
  unfold not.
  intro is_nil.
  unfold g in gt_is_result.
  rewrite is_nil in gt_is_result.
  simpl in gt_is_result.
  discriminate gt_is_result.
Qed.

Open Scope type_scope.
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
  : {gt_block_number & 
      {gt : Block gt_block_number 
        & (g T = Some (existT _ gt_block_number gt)) * (Prefix gs gt)}
    }.
Proof.
  remember (g T) as gt_out.
  unfold g in Heqgt_out.
  pose (superset_has_subset_majority_blocks S T is_sub_set) as supermajority_s_subset_t.
  pose (gt_some_implies_supermajority_not_empty S gs gs_is_result) 
    as supermajority_s_not_nil.
  unfold g in gs_is_result.
Admitted.

Close Scope type_scope.


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
