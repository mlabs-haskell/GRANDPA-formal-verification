Require List.
Require Import Nat.

Require Import Blocks.
Require Import Votes.



Definition find_highest_block_join
  (acc:list AnyBlock)
  (existencial:AnyBlock) 
  : list AnyBlock
    := 
  match acc with
  | List.nil => List.cons existencial List.nil
  | List.cons (existT _ h_block_number _) others =>
    match existencial with
    | existT _ block_number block =>
         if h_block_number <? block_number 
         then List.cons existencial List.nil
         else 
          if Nat.eqb h_block_number  block_number 
          then List.cons existencial acc
          else
            acc
    end
  end.

Lemma find_highest_block_join_never_none (existencial:AnyBlock) (blocks: list AnyBlock) 
  : find_highest_block_join blocks existencial <> nil.
Proof.
  intro H.
  destruct blocks as [|[h_block_number] remain];simpl in H.
  - inversion H.
  - destruct existencial as [block_number].
    destruct (h_block_number <? block_number).
    + inversion H.
    + destruct (h_block_number =? block_number);inversion H.
Qed.

Lemma find_highest_block_join_monotone (existencial:AnyBlock) (blocks:list AnyBlock) 
  {block_results : list AnyBlock}
  : find_highest_block_join blocks existencial = block_results
  -> forall result_block, 
    List.In result_block block_results 
      -> projT1 existencial <= projT1 result_block
          /\ 
          forall block, List.In block blocks 
            -> projT1 block <= projT1 result_block.
Proof.
  intros H result_block H2.
  split.
  Admitted.

Definition find_highest_blocks (blocks:list AnyBlock): list AnyBlock
  := 
  List.fold_left find_highest_block_join blocks List.nil .


Lemma find_highest_blocks_none_iff_nil (blocks: list AnyBlock) 
  : find_highest_blocks blocks = nil <-> blocks = nil.
Proof.
  split.
  - intro H.
    unfold find_highest_blocks in H.
    destruct blocks as [|block blocks].
    + reflexivity.
    +
      Search List.fold_right.
      rewrite <- List.fold_left_rev_right in H.
      simpl in H.
      Admitted.


Lemma find_highest_blocks_works (blocks: list AnyBlock) 
  :forall (n:nat) (block1:Block n) (m:nat) (block2: Block m)
    ,List.In (existT _ m block2) blocks
      -> m <= n.
Proof.
  intros n b1 Hb1.
  induction blocks as [| h_block remain_blocks HInd].
  Admitted.

Lemma find_highest_blocks_have_same_lenght blocks 
  :forall (n:nat) (block1:Block n) (m:nat) (block2: Block m)
    ,List.In (existT _ n block1) blocks
    -> List.In (existT _ m block2) blocks
      -> n = m.
Proof.
  Admitted.

Lemma find_highest_blocks_is_part_of_blocks (blocks:list AnyBlock)
  : forall block, List.In block (find_highest_blocks blocks) -> List.In block blocks.
Proof.
  Admitted.

Lemma find_highest_blocks_outpu_is_unique (blocks:list AnyBlock)
  b 
  : ListFacts.count anyblock_eqb b (find_highest_blocks blocks) <=0.
Proof.
  Admitted.

Lemma find_highest_blocks_on_safe_set {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  (is_safe_t: is_safe T = true)
  : length (find_highest_blocks (List.map fst (get_supermajority_blocks T))) <=1.
Proof.
  destruct (find_highest_blocks (List.map fst (get_supermajority_blocks T))) as [|b1 remain] eqn:H.
  + auto.
  + destruct remain as [| b2 remain2] eqn:H2.
    - auto.
    - simpl.
      pose (List.in_eq b1 remain) as  b1_in.
      pose (List.in_eq b2 (remain2)) as  b2_in2.
      pose (List.in_cons b1 b2 _ b2_in2) as  b2_in.
      rewrite H2 in b1_in.
      rewrite <- H in b1_in.
      rewrite <- H in b2_in.
      apply find_highest_blocks_is_part_of_blocks in b1_in as b1_in_gt.
      apply find_highest_blocks_is_part_of_blocks in b2_in as b2_in_gt.
      rewrite List.in_map_iff in b1_in_gt.
      rewrite List.in_map_iff in b2_in_gt.
      (* TODO use the supermajority to get that both blocks are related
         then use "find_highest_blocks_have_same_lenght"
         conclude that blocks can't be related, contradiction.
       *)
      Admitted.

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
    match find_highest_blocks (List.map fst blocks_with_super_majority) with
    | List.cons block List.nil => Some block
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
  : {gt_block &
      (g T = Some gt_block) * (Prefix gs (projT2 gt_block))}.
Proof.
  remember (g T) as gt_out eqn:is_gt.
  remember (get_supermajority_blocks S) as super_s eqn:Hsuper_s.
  unfold g in is_gt.
  pose (superset_has_subset_majority_blocks S T is_safe_t  is_sub_set) as supermajority_s_subset_t.
  unfold g in gs_is_result.
  rewrite <- Hsuper_s in gs_is_result.
  assert (List.In (existT _ gs_block_number gs) (find_highest_blocks (List.map fst super_s))) as H.
  {
    destruct (find_highest_blocks (List.map fst super_s) ) as [|s remain_s] eqn:H2.
    + inversion gs_is_result.
    + destruct remain_s as [].
      - simpl.
        left.
        injection gs_is_result.
        auto.
      - inversion gs_is_result.
    }
  apply find_highest_blocks_is_part_of_blocks in H.
  apply List.in_map_iff in H.
Require Import Coq.Program.Equality.
  Admitted.
  (*  inversion H.
  dependent destruction H.
  destruct super_s.
  - contradiction.
  - simpl in gs_is_result.
Admitted.
   *)
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
