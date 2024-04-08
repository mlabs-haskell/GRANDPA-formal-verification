Require Import Blocks.

Require Import Votes.
Require List.
Require Import Nat.



Definition find_highest_blocks_join
  (existencial:AnyBlock) 
  (acc:list AnyBlock)
  : list AnyBlock
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
    end.

Lemma find_highest_blocks_join_never_nil 
  (existencial:AnyBlock) (acc:list AnyBlock) 
  : find_highest_blocks_join existencial acc <> List.nil.
Proof.
  destruct existencial as [block_number block].
  destruct acc as [|h_any_block].
  - discriminate.
  - simpl.
    destruct h_any_block as [h_block_number h_block].
    destruct (h_block_number <? block_number).
    + discriminate.
    + destruct (h_block_number =? block_number);discriminate.
Qed.


Definition find_highest_blocks (blocks:list AnyBlock):list AnyBlock
  := 
  List.fold_right find_highest_blocks_join List.nil blocks.


Lemma find_highest_blocks_nil_iff_nil (blocks: list AnyBlock) 
  : find_highest_blocks blocks = nil <-> blocks = nil.
Proof.
  split.
  - intro H.
    unfold find_highest_blocks in H.
    destruct blocks.
    + reflexivity.
    + simpl in H.
      apply find_highest_blocks_join_never_nil in H.
      contradiction.
  - intro H.
    rewrite H.
    auto.
Qed.


Lemma find_highest_blocks_output_has_same_height (blocks: list AnyBlock) 
  : 
  forall (n:nat) (block1:Block n)
  , List.In (existT _ n block1) (find_highest_blocks blocks)
    -> forall (m:nat) (block2:Block m), 
       List.In (existT _ m block2) (find_highest_blocks blocks) 
        -> n = m.
Proof.
  intros n b1 HinResult m b2 HinResult2.
  induction blocks as [|h_block].
  - simpl in HinResult. 
    contradiction.
  - simpl in HinResult.
    Admitted.

Lemma find_highest_blocks_works (blocks: list AnyBlock) 
  :forall (n:nat) (block1:Block n)
    , List.In (existT _ n block1) (find_highest_blocks blocks)
    -> forall (m:nat) (block2:Block m)
      ,List.In (existT _ m block2) blocks
      -> m <= n.
Proof.
  intros n b1 Hb1.
  induction blocks as [| h_block remain_blocks HInd].
  - simpl. 
    intros m b2 f.
    contradiction.
  - intros m b2 H.
    simpl in H.
    destruct H as [is_head|in_remain].
    2:{ simpl in Hb1. Admitted.


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
  match   
    find_highest_blocks (List.map fst blocks_with_super_majority) 
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
  remember (g T) as gt_out eqn:is_gt.
  remember (get_supermajority_blocks S) as super_s eqn:Hsuper_s.
  unfold g in is_gt.
  pose (superset_has_subset_majority_blocks S T is_sub_set) as supermajority_s_subset_t.
  pose (gt_some_implies_supermajority_not_empty S gs gs_is_result) 
    as supermajority_s_not_nil.
  unfold g in gs_is_result.
  rewrite <- Hsuper_s in supermajority_s_not_nil.
  rewrite <- Hsuper_s in gs_is_result.
  destruct super_s.
  - contradiction.
Admitted.
(* - pose (supermajority_s_subset_t (projT1 p) (projT2 p)). *)

(*
plan:
   - Probar que si dos bloques B1 y B2 no estan relacionados pero tienen
   supermajoria en S entonces decendidendo por la funcion de supermajorya 
   eventualmente llegamos a que en conjunto hay al menos n + f +1 -f =  n+1 votos
   contradiccion, por lo que todos los bloques con supermajoria estan 
   en una misma cadena.
   - Para esto agregar la propiedad  de decibilidad de ser prefijo de bloques
   - Para finalizar la prueba is la lista que se contruye en g para buscar 
      el bloque de mayor tamano, es no vacia y tiene mas de un elemento
      , entonces estan no relacionados, pero ambos vienen de supermajoria 
   contradiciendo el inicio.
 *)

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
