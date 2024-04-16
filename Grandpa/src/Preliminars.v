Require List.
Require Import Nat.

Require Import Blocks.
Require Import Votes.



Definition find_highest_block_join
  (existencial:AnyBlock) 
  (acc:list AnyBlock)
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

Lemma find_highest_block_join_never_nil (existencial:AnyBlock) (blocks: list AnyBlock) 
  : find_highest_block_join existencial blocks <> nil.
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
  (blocks_has_same_height: exists n, forall block, List.In block blocks -> (projT1 block) = n )
  :forall result_block, 
    List.In result_block (find_highest_block_join existencial blocks)
      -> projT1 existencial <= projT1 result_block
          /\ 
          forall block, List.In block blocks 
            -> projT1 block <= projT1 result_block.
Proof.
  intros [block_number block] H.
  destruct existencial as [e_block_number e_block].
  destruct blocks_has_same_height as [n blocks_has_same_height].
  simpl in H.
  Admitted.

Definition find_highest_blocks (blocks:list AnyBlock): list AnyBlock
  := 
  List.fold_right find_highest_block_join List.nil blocks .


Lemma find_highest_blocks_nil_iff_nil (blocks: list AnyBlock) 
  : find_highest_blocks blocks = nil <-> blocks = nil.
Proof.
  split.
  - intro H.
    unfold find_highest_blocks in H.
    destruct blocks as [|block blocks].
    + reflexivity.
    +
      simpl in H.
      apply find_highest_block_join_never_nil in H.
      inversion H.
  - intros H.
    rewrite H.
    simpl.
    reflexivity.
Qed.


Lemma find_highest_blocks_works (blocks: list AnyBlock) (b1 b2:AnyBlock)
    :List.In b1 (find_highest_blocks blocks)
    -> List.In b2 blocks
      -> projT1 b2 <= projT1 b1.
Proof.
  intros Hb1.
  induction blocks as [| h_block remain_blocks HInd].
  - intros H.
    simpl in H.
    contradiction.
  - intros H.
  Admitted.

Lemma find_highest_blocks_have_same_lenght blocks 
  :forall (n:nat) (block1:Block n) (m:nat) (block2: Block m)
    ,List.In (existT _ n block1) (find_highest_blocks blocks)
    -> List.In (existT _ m block2) (find_highest_blocks blocks)
      -> n = m.
Proof.
  (* 
    consequence of find_highest_blocks_works
     (maybe we need to prove this to proof find_highest_blocks_works ?)
  *)
  Admitted.

Lemma find_highest_blocks_is_part_of_blocks (blocks:list AnyBlock)
  : forall block, List.In block (find_highest_blocks blocks) -> List.In block blocks.
Proof.
  (*
    all functions refine the list of blocks, trivial.
  *)
  Admitted.

Lemma find_highest_blocks_outpu_is_unique (blocks:list AnyBlock)
  b 
  : forall n, ListFacts.count anyblock_eqb b blocks <=n
   -> ListFacts.count anyblock_eqb b (find_highest_blocks blocks) <=1.
Proof.
  Admitted.

Lemma find_highest_blocks_on_safe_set_lenght {bizantiners_number last_block_number}
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
    - exfalso.
      simpl.
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
      destruct b1_in_gt as [[b1_2 b1_votes] [b1_with_votes_fst_eq b1_with_votes_in ]].
      simpl in b1_with_votes_fst_eq.
      rewrite b1_with_votes_fst_eq in b1_with_votes_in.
      destruct b2_in_gt as [[b2_2 b2_votes] [b2_with_votes_fst_eq b2_with_votes_in ]].
      simpl in b2_with_votes_fst_eq.
      rewrite b2_with_votes_fst_eq in b2_with_votes_in.
      pose (blocks_with_super_majority_are_related T is_safe_t b1 b2 _ _ b1_with_votes_in b2_with_votes_in) as related.
      destruct b1 as [b1_number b1_block].
      destruct b2 as [b2_number b2_block].
      pose (find_highest_blocks_have_same_lenght _ _ b1_block _ b2_block b1_in b2_in) as b1_number_eq_b2_number.
      destruct related as [related|related|related].
      * destruct related.
        simpl in block_number_is_above.
        rewrite b1_number_eq_b2_number in block_number_is_above.
        apply (PeanoNat.Nat.lt_irrefl _ block_number_is_above).
      * destruct related.
        simpl in block_number_is_above.
        rewrite b1_number_eq_b2_number in block_number_is_above.
        apply (PeanoNat.Nat.lt_irrefl _ block_number_is_above).
      * assert (1< ListFacts.count anyblock_eqb (existT _ b1_number b1_block)  (find_highest_blocks (List.map fst (get_supermajority_blocks T)))) as contra1.
        {
          rewrite H.
          unfold ListFacts.count.
          simpl.
          rewrite eqb_reflexive.
          simpl.
          simpl in related.
          rewrite related.
          simpl.
          unfold lt.
          apply le_n_S.
          apply le_n_S.
          apply le_0_n.
        }
      pose (find_highest_blocks_outpu_is_unique (List.map fst (get_supermajority_blocks T)) (existT _ b1_number b1_block) 1) as contra2.
      apply (Arith_base.lt_not_le_stt 1 _ contra1).
      apply contra2.
      unfold get_supermajority_blocks.
      (* use Dictionary.wellformed_means_unique_elements
         and the fact that (not proved yet) filter is monotone with respect to count.*)
      Admitted.

Lemma find_highest_blocks_on_safe_set {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  (is_safe_t: is_safe T = true)
  : get_supermajority_blocks T <> nil 
    -> {b & 
        find_highest_blocks 
          (List.map fst (get_supermajority_blocks T)) = b::nil 
      }.
Proof.
  intro Hnil.
  destruct (find_highest_blocks (List.map fst (get_supermajority_blocks T))) as [| b ls] eqn:Hn.
  - pose (find_highest_blocks_nil_iff_nil (List.map fst (get_supermajority_blocks T)) ) as nil_iff.
    rewrite nil_iff in Hn.
    apply List.map_eq_nil in Hn.
    contradiction.
  - destruct ls as [| contrah contra].
    + refine (existT _ b _ ).
      reflexivity.
    + pose (find_highest_blocks_on_safe_set_lenght T is_safe_t) as H.
      rewrite Hn in H.
      simpl in H.
      apply le_S_n in H.
      apply PeanoNat.Nat.nle_succ_0 in H.
      contradiction.
Qed.

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


(**
  The one in List.in_map_iff is of type Prop, this means 
   we can't destruct the generated term.
*)
Lemma in_map {A B} (f : A -> B) (l : list A) (y : B)
  : List.In y (List.map f l) -> {x : A & f x = y /\ List.In x l}.
Admitted.

Lemma map_in {A B} (f : A -> B) (l : list A) (y : B) (x : A)
  : (f x = y /\ List.In x l) ->List.In y (List.map f l).
Admitted.

Lemma from_g_to_votes_safe_set {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  (is_safe_t:is_safe T = true)
  (gt_anyblock:AnyBlock)
  (gt_is_result : g T = Some gt_anyblock)
  : {vote_number:nat & List.In (gt_anyblock,vote_number) (get_supermajority_blocks T)}.
Proof.
  destruct gt_anyblock as [gt_block_number gt_block] eqn:Hremember.
  pose (gt_some_implies_supermajority_not_empty T gt_block gt_is_result) as super_t_not_nil.
  pose (find_highest_blocks_on_safe_set T is_safe_t super_t_not_nil) as g_t_result.
  destruct g_t_result as [b eq_b].
  unfold g in gt_is_result.
  clear super_t_not_nil.
  rewrite eq_b in gt_is_result.
  injection gt_is_result as b_is_gt.
  rewrite <- Hremember in b_is_gt.
  rewrite b_is_gt  in eq_b.
  pose (List.in_eq gt_anyblock nil) as gt_in_find.
  rewrite <- eq_b in gt_in_find.
  apply (find_highest_blocks_is_part_of_blocks (List.map fst (get_supermajority_blocks T)) gt_anyblock) in gt_in_find.
  apply in_map in gt_in_find.
  destruct gt_in_find as [[gt_anyblock2 gt_votes] [gt_eq gt_in_super_t] ].
  simpl in gt_eq.
  rewrite gt_eq in gt_in_super_t.
  rewrite Hremember in gt_in_super_t.
  refine (existT _ gt_votes gt_in_super_t).
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
    (g T = Some gt_block) * (Related gs (projT2 gt_block) * (gs_block_number <= projT1 gt_block))}.
Proof.
  remember (get_supermajority_blocks S) as super_s eqn:Hsuper_s.
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
  apply find_highest_blocks_is_part_of_blocks in H as H2.
  apply in_map in H2.
  destruct H2 as [[gs_anyblock gs_votes] [gs_eq gs_in_super]].
  rewrite Hsuper_s in gs_in_super.
  apply supermajority_s_subset_t in gs_in_super.
  destruct gs_in_super as [gs_votes_in_t gs_in_super_t].
  remember (gs_anyblock,gs_votes_in_t) as gs_with_votes_in_t.
  assert (fst gs_with_votes_in_t = existT (fun n : nat => Block n) gs_block_number gs) as Haux1.
  {
    rewrite Heqgs_with_votes_in_t.
    simpl.
    simpl in gs_eq.
    assumption.
    }
  assert (
   fst gs_with_votes_in_t = gs_anyblock /\ List.In gs_with_votes_in_t (get_supermajority_blocks T)) as Haux2.
   {
     split.
     - simpl in gs_eq.
       rewrite gs_eq.
       assumption.
     - assumption.
     }
  pose (map_in fst (get_supermajority_blocks T) gs_anyblock gs_with_votes_in_t Haux2) as gs_anyblock_in_map_t.
  assert (get_supermajority_blocks T <> nil) as super_t_not_nil.
  {
    unfold not.
    intros H3.
    rewrite H3 in gs_in_super_t.
    apply (List.in_nil gs_in_super_t).
  }
  pose (find_highest_blocks_on_safe_set T is_safe_t super_t_not_nil) as g_t_result.
  destruct g_t_result as [gt_anyblock gt_eq].
  assert (g T = Some gt_anyblock ) as gt_result.
  {
    unfold g.
    rewrite gt_eq.
    reflexivity.
  } 
  (* pose (from_g_to_votes_safe_set T is_safe_t _ gt_result ) as gt_in_super_t. *)
  pose (List.in_eq gt_anyblock nil) as gt_in_find.
  rewrite <- gt_eq in gt_in_find.
  apply find_highest_blocks_is_part_of_blocks in gt_in_find as gt_in_map.
  apply in_map in gt_in_map.
  destruct gt_in_map as [[gt_block gt_votes] [gt_eq2 gt_in_super_t] ].
  simpl in gt_eq2.
  rewrite gt_eq2 in gt_in_super_t.
  rewrite Heqgs_with_votes_in_t in gs_in_super_t.
  pose (blocks_with_super_majority_are_related T is_safe_t gs_anyblock gt_anyblock gs_votes_in_t gt_votes gs_in_super_t gt_in_super_t) as related.
  simpl in gs_eq.
  rewrite gs_eq in related.
  simpl in related.
  rewrite gs_eq in gs_anyblock_in_map_t.
  pose (find_highest_blocks_works (List.map fst (get_supermajority_blocks T)) gt_anyblock (existT _ gs_block_number gs) gt_in_find gs_anyblock_in_map_t) as gs_number_leq_gt_number.
  refine (existT _ gt_anyblock (gt_result, (related, gs_number_leq_gt_number))).
Qed.
  

  (* TODO 
    use that "find_highest_blocks_on_safe_set" to get a single block in 
     find_highest_blocks output
    destructure gt until we conclude gt in get_supermajority_blocks T.
    find that they must be related.
    by "find_highest_blocks_works" they can be the same or gs < gt.
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
