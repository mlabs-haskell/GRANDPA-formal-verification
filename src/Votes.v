Require List.
Require Import  Nat.
Require Import Coq.Program.Equality.

Require Dictionary.
Require Import Blocks.

(** * Voters 
*)

(** 
Some requirements about a type that can represent voters:
   - It must have infinite inhabitants.
   - It must have decidable equality.
This means, we can have any number of voters and we can 
distinguish between them. 
For this reason we choose to use naturals.
*)
Definition Voter : Type := nat.


(**
  The bizantiners_number parameter isn't used 
   in the definition of the type, we 
   leave it open to any assumption. 
   Previously we had a constraint but 
   it wasn't useful and only complicate things.

  Ideally a Voters must be proper set, but we 
   don't want to complicate much the types.
  We may add a constraint in the constructor 
   to ensure that no voter is repeated in the 
   list, but it may complicate construction of 
   voters.

  Why not [Definition Voters nat := list Voter]?
  this would be equivalent to [list nat]. 
   We are going to work with multiple things 
   that are equivalent to [list nat]. This 
   means we should use the newtype pattern here.

  Note: Coq doesn't have a newtype syntax as 
   in Haskell, so we should use a variant.
*)
Variant Voters (bizantiners_number:nat) : Type 
  := 
    | VotersC (voters:list Voter) 
        (*
           TODO: 
            add a constraint here to make the voters to only appear 
            once, or use a proper set.
           For now we assume that voters are registered only once.
          *)
      : Voters  bizantiners_number .


Definition voters_to_list {bizantiners_number} (voters:Voters bizantiners_number)
  := 
  match voters with
  | VotersC _ l => l
  end.

Definition voters_length {bizantiners_number} (voters:Voters bizantiners_number)
  := 
  length (voters_to_list voters).

Definition in_Voters {bizantiners_number} 
  (voter : Voter) (voters:Voters bizantiners_number) 
  :=
  List.In voter (voters_to_list voters).


Definition in_Voters_bool {bizantiners_number} 
  (voter : Voter) (voters:Voters bizantiners_number) 
  := 0 <? (List.count_occ PeanoNat.Nat.eq_dec (voters_to_list voters) voter).

(** * Votes
*)

(** ** Vote

From the paper:

<<
  A vote is a block hash, together with some metadata such as round number 
  and the type of vote, such as prevote or precommit, all signed with a 
  voter’s private key
>>
  
Following the same approach as with the Blocks, we choose to replace the 
block hash with the real block. This makes proofs easier.

Round number would be added later when we add Time and Rounds, this 
  simplifies the work with a Vote.

We don't have types for votes, instead when needed, we distinguish
them by maintaining two different set of votes, one for precommits 
and other for previews.

However, we want to tie a Vote with a particular set of Voters 
and to ensure that the Vote is coherent.

Additionally a Vote depends on the [last_block], this is 
we are only interested in the blocks that are children of 
[last_block]. 

This means that [last_block] can be often interpreter as the 
_last_block_finalized_.
However this may not be the case in particular situations.
*)

Variant Vote {bizantiners_number last_block_number}
  (voters: Voters bizantiners_number )
  (original_chain:Block last_block_number)
  :Type 
  := 
    | VoteC {m}  (voter : Voter) 
      (is_voter: in_Voters voter voters ) 
      (block: Block m) (is_prefix: Prefix original_chain block)
      : Vote voters original_chain.

Definition vote_to_voter {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number}
  {original_chain:Block last_block_number}
  (vote: Vote voters original_chain)
  : Voter
  :=
  match vote with 
  | VoteC _ _ voter _ _ _ => 
      voter
  end.


Definition vote_to_pair  {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number}
  {original_chain:Block last_block_number}
  (vote: Vote voters original_chain)
  : (nat * (sigT (fun n => Block n)))
  :=
  match vote with 
  | VoteC _ _ voter _ block _ => 
        (voter , existT _ _ block)
  end.


(** ** Votes
  As with [Voters], we choose to use the newtype pattern here.
*)
Inductive Votes  {bizantiners_number last_block_number}
  (voters: Voters bizantiners_number) (last_block:Block last_block_number)
  :Type 
  := 
    | VotesC
      (votes_list:list (Vote voters last_block))
      : Votes voters last_block.

Definition votes_to_list {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number} {last_block:Block last_block_number}
  (votes: Votes voters last_block)
  : list (Vote voters last_block)
  := 
  match votes with
  | VotesC _ _ l => l
  end.

Definition votes_to_voters_list {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number} {last_block:Block last_block_number}
  (votes: Votes voters last_block)
  : list Voter
  := List.map vote_to_voter (votes_to_list votes).

Definition votes_to_pair_list {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number} {last_block:Block last_block_number}
  (votes: Votes voters last_block)
  : list (nat * (sigT (fun n => Block n)))
  := List.map vote_to_pair (votes_to_list votes).

Definition voter_voted_in_votes {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number} {last_block:Block last_block_number}
  (voter: Voter)
  (votes: Votes voters last_block)
  :=
  0 <?
    List.length(
    List.filter 
      (fun vote => Nat.eqb voter (vote_to_voter vote)) 
      (votes_to_list votes)).


Definition is_equivocate {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (voter: Voter)
  (votes: Votes voters last_block)
  : bool
  :=
      let voters_list : list Voter 
        := votes_to_voters_list votes
      in
      let filtered := List.filter (Nat.eqb voter) voters_list
      in
        1 <? (length filtered).

(**
The first element are the equivocate voters 
and the second one are the voters that only voted once.


Why?

In Purescript the partition funtion returns a record like:

<<
  {success: _ , failures: _} 
>>

Then you can do [out.success] and [out.failures]. 

In coq that may be not worth the effort.
*)

Definition split_voters_by_equivocation {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block)
  : list Voter * list Voter
  :=
    let voters_list := voters_to_list voters
    in
      List.partition  (fun voter => is_equivocate voter votes) voters_list.

Open Scope list.

Lemma non_equivocate_votes_are_unique {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block)
  {equivocate_voters non_equivocate_voters}
  (eq_split : (equivocate_voters,non_equivocate_voters) = split_voters_by_equivocation votes)
  : 
  forall x l1 l2, non_equivocate_voters  = l1++ (x::l2) -> not (List.In x (l1++l2)).
Proof.
  intros x l1 l2 H HIn.
  pose (List.in_elt x l1 l2) as xIn.
  rewrite <- H in xIn.
  unfold split_voters_by_equivocation in eq_split.
  pose (List.partition_as_filter (fun voter => is_equivocate voter votes) (voters_to_list voters) ).
  rewrite e in eq_split.
  inversion eq_split.
  rewrite H2 in xIn.
  rewrite List.filter_In in xIn.
  destruct xIn as [xIn x_true].
  Admitted.


Close Scope list.


Section Some.

(** 
  Sections are really useful to declare local variables 
   to avoid having big predicates.
   But sometimes we may need to close a section since 
   coq interprets in a erroneous way what we write.
   We immediately open a section again when this happen.
*)
Context {bizantiners_number last_block_number : nat}.
Variable voters: Voters bizantiners_number.
Variable last_block  :Block last_block_number.
Variable votes: Votes voters last_block.

Definition in_nat_list (n:nat) (l:list nat) :bool := 
  match List.find (fun m => Nat.eqb n m) l with
  | None => false
  | _ => true
  end.

Definition filter_votes_by_voters_subset (subset : Voters bizantiners_number ) 
  : Votes voters last_block
  := 
  let votes_list := votes_to_list votes
  in
  let voters_as_nat_list := voters_to_list subset
  in
  let vote_predicate vote := in_nat_list (vote_to_voter vote) voters_as_nat_list
  in
    VotesC voters last_block (List.filter vote_predicate  votes_list).
    
End Some.



Definition is_safe {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block)
  :bool
  :=
  match split_voters_by_equivocation votes with
  | (equivocate_voters, non_equivocate_voters) =>
     length equivocate_voters <=? bizantiners_number
  end.



Module BlockDictionaryTypes <: Dictionary.Types.
  Definition K := AnyBlock.
  Definition V := nat.
  Definition eqb := any_block_eqb.
End BlockDictionaryTypes.

Module BlockDictionaryModule := Dictionary.Functions BlockDictionaryTypes.

Definition BlockDictionary := BlockDictionaryModule.Dictionary AnyBlock nat.

(** ** Vote count
*)

(**
  A vote for [B: Block n] is also a vote for [B':Block n'] 
   as long as [B' <= B] ([Prefix B' B]). 

  This function takes a block and add a vote to the [acc] dictionary
   for every block that is above the [last_block].
*)
Fixpoint count_vote_aux {last_block_number vote_block_number}
  {last_block : Block last_block_number}
  (vote_block:Block vote_block_number)
  (prefix_proof : Prefix last_block vote_block)
  (acc: BlockDictionary): BlockDictionary
  :=
    match prefix_proof with
    | Same _ _=> acc
    | IsPrefix _ older_block _ new_prefix_proof =>
       let update_vote maybe_old_value v := 
         match maybe_old_value with
         | None => v
         | Some v2 => v+v2
         end
       in
       let updated_acc := BlockDictionaryModule.update_with (existT _ vote_block_number vote_block) update_vote acc
       in 
        count_vote_aux older_block new_prefix_proof updated_acc    
    end.

(** 
  Coq refuses to evaluate functions that use fixpoint
   unless all it's arguments are already evaluted.
   This made us split the fixpoint functions in two or more
   functions to attempt to maximize the unfolding of functions.
*)
Definition count_vote {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (vote :Vote voters last_block) (acc: BlockDictionary): BlockDictionary
  :=
  match vote with
  | VoteC _ _ _ _ block prefix_proof => count_vote_aux block prefix_proof acc
  end.

(**
The first element of the output is the list of votes that remains to 
be considered.
*)

Fixpoint count_votes_aux {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes:list (Vote voters last_block)) (acc: BlockDictionary): (list (Vote voters last_block)) * BlockDictionary
  :=
  match votes with
  | List.nil => (List.nil, acc)
  | List.cons vote remain => count_votes_aux remain (count_vote vote acc)
  end.

(** 
  Takes a set of votes and returns a dictionary of blocks
   where the value for a block is the number of votes for that 
   block.

  We have to use AnyBlock here since the Dictionary 
   contains blocks of different lengths.
*)
Definition count_votes {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block): BlockDictionary
  :=
  match count_votes_aux (votes_to_list votes) BlockDictionaryModule.empty with
  | (_ , out) => out
  end.


(**
  This is the core function implementing supermajority.

   From the paper: 

<<
A voter equivocates in a set of votes [S] if they have cast multiple different 
votes in [S] . We call a set [S] of votes safe if the number of voters 
who equivocate in [S] is at most [f] . We say that [S] has a [supermajority]
for a block [B] if the set of voters who either have a vote for 
blocks [>= B] or equivocate in [S] has size at least [(n+f + 1)/2]. 
We count equivocations as votes for everything so that observing a vote 
is monotonic, meaning that if [S ⊂ T] then if [S] has a supermajority 
for [B] so does [T] , while being able to ignore yet more equivocating votes
from an equivocating voter.
>>

Our implementation aproach is as follows:

   - Find the equivocate votes and the ones that aren't equivocate.
   - Count the non equivocate votes for every block.
   - Remove blocks that don't have at least [(n+f+1)/2] votes.
      In this case [n:=length voters] and [f:= bizantiners_number]
*)
Definition get_supermajority_blocks {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  : list (AnyBlock * nat)
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
    blocks_with_super_majority.


(**
This definition doesn't take in account the repetitions of elements
*)
Definition IsSubset {bizantiners_number last_block_number} 
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S : Votes voters last_block)
  (T : Votes voters last_block) 
  :Prop
  :=
  forall (vote: Vote voters last_block), 
    List.In vote (votes_to_list S)
    -> List.In vote (votes_to_list T).

Lemma aux {A} (l l1 l2:list A) p 
  : 
  List.partition p l = (l1,l2) 
  -> forall x, List.In x l1 
  -> p x = true. 
Proof.
  Admitted.


Lemma equivocates_are_voters {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  {equivocate_voters non_equivocate_voters: list Voter}
  {split_result: split_voters_by_equivocation T = (equivocate_voters,non_equivocate_voters)}
  : forall (voter:Voter), 
    List.In voter equivocate_voters
    -> List.In voter (votes_to_voters_list T).
Proof.
  intros voter equivocated.
  unfold split_voters_by_equivocation in split_result.
  assert (List.In voter (voters_to_list voters)) as in_voters_list.
  {
    pose 
      (List.elements_in_partition 
        (fun voter => is_equivocate voter T) 
        (voters_to_list voters) 
        split_result
      ) as is_element_iff .
    apply is_element_iff.
    left.
    assumption.
  }
  pose 
    (aux 
      (voters_to_list voters) 
      equivocate_voters 
      non_equivocate_voters 
      (fun voter => is_equivocate voter T)
      split_result
      voter
      equivocated
    ) as H.
    simpl in H.
    unfold is_equivocate in H.
    rewrite PeanoNat.Nat.ltb_lt in H.
    remember (List.filter (Nat.eqb voter) (votes_to_voters_list T) ) as filtered_list.
    destruct filtered_list as [|one_elem remain].
    - simpl in H.  
      pose (PeanoNat.Nat.nlt_succ_diag_l 0) as contra.
      contradiction.
    - pose (List.in_eq one_elem remain) as in_left_list.
      rewrite Heqfiltered_list in in_left_list.
      pose (List.filter_In (Nat.eqb voter) one_elem (votes_to_voters_list T)) as iff.
      rewrite iff in in_left_list.
      destruct in_left_list.
      apply (PeanoNat.Nat.eqb_eq voter one_elem) in H1.
      rewrite <- H1 in H0.
      assumption.
Qed.

(**
   S ⊂ T => eqivocates_in_S ⊂ equivocates_in_T
*)
Lemma superset_has_equivocates_of_subset {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S : Votes voters last_block) 
  (T : Votes voters last_block) 
  (is_subset: IsSubset S T)
  {equivocate_voters_s non_equivocate_voters_s: list Voter}
  {equivocate_voters_t non_equivocate_voters_t: list Voter}
  {split_s_result:(equivocate_voters_s,non_equivocate_voters_s) = split_voters_by_equivocation S}
  {split_t_result:(equivocate_voters_t,non_equivocate_voters_t) = split_voters_by_equivocation T}
  : forall (voter:Voter), 
    List.In voter equivocate_voters_s 
    -> List.In voter equivocate_voters_t.
Proof.
  intro voter.
  intro is_equivocate_s.
  Admitted.


(**
From the paper:

<<
We count equivocations as votes for everything so that observing a vote is 
monotonic, meaning that if [S ⊂ T] then if [S] has a supermajority 
for [B] so does [T] , while being able to ignore yet more equivocating votes 
from an equivocating voter.
>>
  
*)
Lemma blocks_with_super_majority_are_related {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  : forall (block1 block2:AnyBlock) (v1 v2:nat), 
    List.In (block1,v1) (get_supermajority_blocks T)
    -> List.In (block2,v2) (get_supermajority_blocks T)
    -> Related (projT2 block1) (projT2 block2).
Proof.
  intros ab1 ab2 v1 v2 H1 H2.
  destruct ab1 as [n1 b1] eqn:Hab1.
  destruct ab2 as [n2 b2] eqn:Hab2.
  simpl.
  remember (get_supermajority_blocks T) as gt eqn:Heq_gt.
  unfold get_supermajority_blocks in Heq_gt.
  remember (split_voters_by_equivocation T) as splitedT.
  destruct splitedT as [equivocated_voters non_equivocate_voters].
  rewrite Heq_gt in H1.
  rewrite (List.filter_In) in H1.
  destruct H1 as [count1 ineq1].
  rewrite Heq_gt in H2.
  rewrite (List.filter_In) in H2.
  destruct H2 as [count2 ineq2].
  rewrite PeanoNat.Nat.ltb_lt in ineq1.
  rewrite PeanoNat.Nat.ltb_lt in ineq2.
  pose (PeanoNat.Nat.add_lt_mono _ _ _ _ ineq1 ineq2) as ineq.
  (* Search (?n * ?m < ?n * ?w). *)

  Admitted.

Lemma superset_has_subset_majority_blocks {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S : Votes voters last_block) 
  (T : Votes voters last_block) 
  (safe_proof: is_safe T=true)
  (is_subset: IsSubset S T)
  : forall anyblock anyblock_votes, 
      List.In (anyblock,anyblock_votes) (get_supermajority_blocks S)
      -> exists anyblock_votes_in_t 
          , List.In (anyblock,anyblock_votes_in_t) (get_supermajority_blocks T).
Proof.
Admitted.
  

Definition has_supermajority  {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S : Votes voters last_block) 
  : bool
  := 
  0 <? length (get_supermajority_blocks S) .


(**
   Since Votes is a wrap around a list, this function wraps [++].
*)
Definition mergeVotes {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes1 :Votes voters last_block)
  (votes2 :Votes voters last_block)
  : Votes voters last_block
  :=
    match votes1, votes2 with
      | VotesC _ _ list1, VotesC _ _ list2 => VotesC _ _ (list1 ++ list2)
      end.
