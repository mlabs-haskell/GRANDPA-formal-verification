Require List.
Require Import  Nat.
Require Import Coq.Program.Equality.
Require Coq.Program.Wf.
Require Import Lia.

Require Dictionary.
Require Import Blocks.
Require Import ListFacts.

Require Import Sets.

Open Scope bool.
Open Scope blocks_scope.

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
  Note: Coq doesn't have a newtype syntax as 
   in Haskell, so we should use a variant.
*)

Record Voters : Type 
  := {get_voters_dictionary: DictionarySet Voter
      ;round_number_of_voters: nat
  }.

Definition voters_to_list (voters:Voters)
  := Sets.to_list (get_voters_dictionary voters).

Definition voters_length (voters:Voters)
  := 
  length (voters_to_list voters).

Definition voters_from_list (voters:list Voter) 
  (round_number_of_voters:nat)
  : Voters
  := {| get_voters_dictionary:= Sets.from_list Nat.eqb voters
        ;round_number_of_voters:=round_number_of_voters
    |}.

Definition voters_voters_and_list 
  (voters:Voters)
  (ls:list Voter)
  : Voters 
  :=
  voters_from_list ls voters.(round_number_of_voters) .



Definition in_Voters
  (voter : Voter) 
  (voters:Voters) 
  :=
  List.In voter (voters_to_list voters).


Definition in_Voters_bool  
  (voter : Voter) (voters:Voters) 
  := 0 <? (List.count_occ PeanoNat.Nat.eq_dec (voters_to_list voters) voter).


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
and other for prevotes.

However, we want to tie a Vote with a particular set of Voters 
and to ensure that the Vote is coherent.
*)

Variant Vote
  (voters: Voters)
  :Type 
  := 
  | VoteC {m} (voter : Voter) 
      (is_voter: in_Voters voter voters ) 
      (block: Block m) 
      : Vote voters.

Definition vote_to_voter 
  {voters: Voters }
  (vote: Vote voters)
  : Voter
  :=
  match vote with 
  | VoteC _ voter _ _ => 
      voter
  end.


Definition vote_to_pair 
  {voters: Voters}
  (vote:Vote voters)
  : Voter * AnyBlock 
  :=
  match vote with 
  | VoteC _ voter _ block => 
        (voter , existT _ _ block)
  end.

Definition vote_to_block  
  {voters: Voters }
  (vote: Vote voters )
  : AnyBlock
  :=
  match vote with 
  | VoteC _ voter _ block => 
        existT _ _ block
  end.

Definition vote_eqb 
  {voters: Voters}
  (vote1 vote2: Vote voters)
  : bool
  :=
  match vote1,vote2 with
  | VoteC _ voter1' _ block1 , VoteC _ voter2' _ block2
      =>
      (voter1' =? voter2')%nat && (block1 =? block2)
  end.


(** ** Votes
  As with [Voters], we choose to use the newtype pattern here.
*)
Inductive Votes  
  (voters: Voters) 
  :Type 
  := 
    | VotesC
      (votes_list:list (Vote voters))
      : Votes voters.

Definition votes_to_list 
  {voters: Voters} 
  (votes: Votes voters)
  : list (Vote voters)
  := 
  match votes with
  | VotesC _ l => l
  end.

Definition votes_to_voters_list 
  {voters: Voters} 
  (votes: Votes voters)
  : list Voter
  := List.map vote_to_voter (votes_to_list votes).

Definition votes_to_pair_list 
  {voters: Voters} 
  (votes: Votes voters )
  : list (nat * AnyBlock)
  := List.map vote_to_pair (votes_to_list votes).

Definition voter_voted_in_votes 
  {voters: Voters} 
  (voter: Voter)
  (votes: Votes voters)
  :=
  0 <? count Nat.eqb voter (votes_to_voters_list votes).


(**
   Since Votes is a wrap around a list, this function wraps [++].
*)
Definition mergeVotes 
  {voters:Voters }
  (votes1 :Votes voters)
  (votes2 :Votes voters)
  : Votes voters
  :=
    match votes1, votes2 with
      | VotesC _ list1, VotesC _ list2 => VotesC _ (list1 ++ list2)
      end.

Definition is_equivocate  
  {voters: Voters}
  (voter: Voter)
  (votes: Votes voters)
  : bool
  := 1 <? count Nat.eqb voter ( votes_to_voters_list votes).

(**
The first element are the equivocate voters 
and the second one are the voters that only voted once.
*)

Definition split_voters_by_equivocation 
  {voters: Voters}
  (votes: Votes voters)
  : list Voter * list Voter
  :=
    let voters_list := voters_to_list voters
    in
      List.partition  (fun voter => is_equivocate voter votes) voters_list.

Section Some.

(** 
  Sections are really useful to declare local variables 
   to avoid having big predicates.
   But sometimes we may need to close a section since 
   coq interprets in a erroneous way what we write.
   We immediately open a section again when this happens.
*)
Variable voters: Voters.
Variable votes: Votes voters.

Definition in_nat_list (n:nat) (l:list nat) :bool := 
  match List.find (fun m => (n =? m)%nat) l with
  | None => false
  | _ => true
  end.

Definition filter_votes_by_voters_subset (subset : Voters) 
  : Votes voters
  := 
  let votes_list := votes_to_list votes
  in
  let voters_as_nat_list := voters_to_list subset
  in
  let vote_predicate vote := in_nat_list (vote_to_voter vote) voters_as_nat_list
  in
    VotesC voters (List.filter vote_predicate  votes_list).
    
End Some.



Definition is_safe  
  {voters: Voters }
  (votes: Votes voters)
  :bool
  :=
  match split_voters_by_equivocation votes with
  | (equivocate_voters, non_equivocate_voters) =>
     length equivocate_voters <=? calculate_max_bizantiners voters 
  end.

Definition BlockDictionary := Dictionary.Dictionary AnyBlock nat.

(** ** Vote count

- First we split the set of votes in two, one of votes 
  made by equivocate voters and other made by 
   non equivocate voters
- We count the total votes for all the block that 
  were votes (that is, we don't count the 
   blocks b such that   b < b'
   when some voter voted for b' but not for b)
- Then we do a "flatten" it means for every 
  voted block b, if b' < b
   then we add the votes for b to the votes for b'.
*)


Definition aux_vote_update (old_votes: option nat) (new_votes:nat)
  := 
  match old_votes with
  | None => new_votes
  | Some v' => new_votes+v'
  end.

Definition update_with_vote_to_block (d:BlockDictionary)
  (block:AnyBlock)
  : BlockDictionary
  := Dictionary.update_with anyblock_eqb block 1 aux_vote_update d.

(*
  This function takes the list of votes (befor flatten)
   and counts the number of votes for every vote
*)
Definition make_votes_dictionary
  (votes:list AnyBlock)(acc: BlockDictionary)
  : BlockDictionary
  :=
  List.fold_left 
  update_with_vote_to_block
  votes
  acc.

Lemma make_votes_dictionary_step_empty
  (votes:list AnyBlock) block
  : make_votes_dictionary (block::votes) Dictionary.empty
    = make_votes_dictionary votes (Dictionary.from_list anyblock_eqb ((block,1)::nil)%list).
Proof.
  simpl.
  enough (
    update_with_vote_to_block Dictionary.empty block
    =
    Dictionary.add anyblock_eqb block 1 Dictionary.empty
  ). auto.
  unfold update_with_vote_to_block.
  reflexivity.
Qed.

(*Lemma make_votes_dictionary_step
  (votes:list AnyBlock) block d
  : make_votes_dictionary (block::votes) d
    = make_votes_dictionary votes (update_with_vote_to_block d block).
Proof.
  simpl.
  enough (
    update_with_vote_to_block Dictionary.empty block
    =
    Dictionary.add anyblock_eqb block 1 Dictionary.empty
  ). auto.
  unfold update_with_vote_to_block.
  reflexivity.
Qed.
 *)

Definition some_to_nat (x:option nat)
  := 
  match x with
     | Some y => y
     | None => 0
  end.

Lemma make_votes_dictionary_counts_right_aux 
  (votes:list AnyBlock)
  : forall block votes_value d,
    Dictionary.lookup anyblock_eqb block (make_votes_dictionary votes d)
      = Some votes_value
    -> votes_value = count anyblock_eqb block votes 
      + some_to_nat (Dictionary.lookup anyblock_eqb block d). 
Proof.
  induction votes.
  - intros block v d H.
    simpl.
    simpl in H.
    rewrite H.
    reflexivity.
  - intros block v d H.
    simpl in H.
    apply IHvotes in H.
    rewrite count_cons.
    enough (
      some_to_nat(
        Dictionary.lookup 
          anyblock_eqb block 
          (update_with_vote_to_block d a)
      )
      =
      (if anyblock_eqb block a then 1 else 0)
        +
      some_to_nat(Dictionary.lookup anyblock_eqb block d)
    ) as H2.
    + rewrite H2 in H.
      lia.
    + unfold update_with_vote_to_block.
      unfold update_with_vote_to_block in H.
      destruct (anyblock_eqb block a) eqn:block_a.
      * rewrite (Dictionary.update_lookup_k_eqb).
        2: assumption.
        simpl.
        unfold aux_vote_update.
        rewrite (Dictionary.lookup_eqb_rewrite anyblock_eqb d (k1:=block) (k2:=a) block_a).
        destruct (Dictionary.lookup anyblock_eqb a d);auto.
      * simpl.
        rewrite Dictionary.update_lookup_keeps_others_k_eqb.
        reflexivity.
        assumption.
Qed.

Lemma make_votes_dictionary_counts_right_aux2
  (votes:list AnyBlock)
  : forall block d,
    some_to_nat (Dictionary.lookup anyblock_eqb block (make_votes_dictionary votes d))
    = count anyblock_eqb block votes 
      + some_to_nat (Dictionary.lookup anyblock_eqb block d). 
Proof.
  induction votes.
  - intros block d.
    simpl.
    reflexivity.
  - intros block d.
    simpl.
    rewrite count_cons.
    rewrite IHvotes.
    enough (
      some_to_nat(
        Dictionary.lookup 
          anyblock_eqb block 
          (update_with_vote_to_block d a)
      )
      =
      (if anyblock_eqb block a then 1 else 0)
        +
      some_to_nat(Dictionary.lookup anyblock_eqb block d)
    ) as H2.
    + rewrite H2.
      lia.
    + unfold update_with_vote_to_block.
      destruct (anyblock_eqb block a) eqn:block_a.
      * rewrite (Dictionary.update_lookup_k_eqb).
        2: assumption.
        simpl.
        unfold aux_vote_update.
        rewrite (Dictionary.lookup_eqb_rewrite anyblock_eqb d (k1:=block) (k2:=a) block_a).
        destruct (Dictionary.lookup anyblock_eqb a d);auto.
      * simpl.
        rewrite Dictionary.update_lookup_keeps_others_k_eqb.
        reflexivity.
        assumption.
Qed.

Lemma make_votes_dictionary_counts_right
  (votes:list AnyBlock)
  : forall (block:AnyBlock),
    some_to_nat (Dictionary.lookup anyblock_eqb block (make_votes_dictionary votes Dictionary.empty))
    = count anyblock_eqb block votes.
Proof.
  intro block.
  rewrite (make_votes_dictionary_counts_right_aux2 votes block Dictionary.empty).
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
Qed.


(**
  A vote for [B: Block n] is also a vote for [B':Block n'] 
   as long as [B' <= B]. 
*)
Fixpoint flat_votes_aux {m}
  (block:Block m)
  (voter_number:nat)
  (acc: BlockDictionary): BlockDictionary
  :=
  match block with  
  | OriginBlock => acc
  | NewBlock older_block id 
      =>
     let update_vote maybe_old_value v := 
       match maybe_old_value with
       | None => v
       | Some v2 => v+v2
       end
     in
     let updated_acc := 
          Dictionary.update_with 
            Blocks.anyblock_eqb
            (existT _ m block) voter_number update_vote acc
     in 
      flat_votes_aux older_block voter_number updated_acc
  end.

Definition flat_votes_dictionary 
  (acc:BlockDictionary) : BlockDictionary
  := 
  List.fold_right 
    (
      fun anyblock updated_dict 
      =>
      match anyblock with
      | (block,votes_for_block)
          => flat_votes_aux 
            (projT2 block) votes_for_block updated_dict
      end
    )
    Dictionary.empty
    (Dictionary.to_list acc ).

(** 
  Takes a set of votes and returns a dictionary of blocks
   where the value for a block is the number of votes (already flattened)
   for that block.

  We have to use AnyBlock here since the Dictionary 
   contains blocks of different lengths.
*)
Definition count_votes 
  {voters:Voters}
  (votes: Votes voters): BlockDictionary
  :=
  match make_votes_dictionary (List.map vote_to_block (votes_to_list votes)) Dictionary.empty with
  | out => flat_votes_dictionary out
  end.

Lemma count_votes_nil_is_zero 
  {voters:Voters}
  (votes: Votes voters)
  : votes_to_list votes = nil 
    -> Dictionary.to_list (count_votes votes) = nil.
Proof.
  intro H.
  unfold count_votes.
  rewrite H.
  reflexivity.
Qed.

Lemma count_votes_works 
  {block_number:nat}
  (block: Block block_number)
  {voters:Voters}
  (votes:Votes voters)
  :
  some_to_nat(
    Dictionary.lookup 
    anyblock_eqb
    (existT _ block_number block) 
    (count_votes votes)
  )
  =length (
       List.filter (
         fun vote => is_prefix block (projT2 (vote_to_block vote))
       ) 
       (votes_to_list votes) 
      ).
Proof.
  unfold count_votes.
  (* TODO: use this rewrite make_votes_dictionary_counts_right.*)
  Admitted.



Lemma voted_block_in_count_votes 
  {voters:Voters }
  (votes: Votes voters)
  {voter:Voter }
  {is_voter: in_Voters voter voters}
  {block_number:nat}
  {block: Block block_number}
  (vote: Vote voters)
  {vote_is: vote = VoteC voters voter is_voter block}
  (is_vote : List.In vote (votes_to_list votes))
  : exists v:nat
    , List.In 
      (existT _ block_number block,v) 
      (Dictionary.to_list (count_votes votes)).
Proof.
  Admitted.
  (*  exists (count_block_votes )
  unfold count_votes.
  apply (List.in_map vote_to_block) in is_vote as block_in_votes.
  unfold make_votes_dictionary.
  unfold make_votes_dictionary_aux.
  simpl.
  simpl. 

  Admitted.
   *)



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
      In this case [n:=length voters] and [f:= ]
*)

Definition has_supermajority_predicate 
  (voters:Voters)
  (number_of_equivocates:nat)
  (block_and_vote:AnyBlock*nat) : bool:= 
    match block_and_vote with
    | (_, number_of_votes) 
        => 
        voters.(round_number_of_voters) 
        + calculate_max_bizantiners voters +1 
        <? 2 * (number_of_votes + number_of_equivocates)
    end.



Definition get_supermajority_blocks 
  {voters:Voters}
  (T : Votes voters) 
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
        T 
        (voters_from_list non_equivocate_voters voters.(round_number_of_voters))
      )
  in
  let blocks_with_super_majority 
    := 
    List.filter 
      (has_supermajority_predicate voters number_of_equivocates)
      (Dictionary.to_list count)
  in
    blocks_with_super_majority.


(**
This definition doesn't take in account the repetitions of elements
*)


Lemma equivocates_are_voters_aux {A} (l l1 l2:list A) p 
  : 
  List.partition p l = (l1,l2) 
  -> forall x, List.In x l1 
  -> p x = true. 
Proof.
  intros H x Hin.
  pose (List.partition_as_filter p l) as H3.
  rewrite H3 in H.
  inversion H.
  rewrite <- H1 in Hin.
  apply List.filter_In in Hin.
  destruct Hin as [_ a].
  assumption.
Qed.


Lemma equivocates_are_voters 
  {voters:Voters}
  (T : Votes voters) 
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
    (equivocates_are_voters_aux 
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
      Admitted.
      (*      contradiction.
    - pose (List.in_eq one_elem remain) as in_left_list.
      rewrite Heqfiltered_list in in_left_list.
      pose (List.filter_In (Nat.eqb voter) one_elem (votes_to_voters_list T)) as iff.
      rewrite iff in in_left_list.
      destruct in_left_list.
      apply (PeanoNat.Nat.eqb_eq voter one_elem) in H1.
      rewrite <- H1 in H0.
      assumption.
Qed.
       *)


(**
From the paper:

<<
We count equivocations as votes for everything so that observing a vote is 
monotonic, meaning that if [S ⊂ T] then if [S] has a supermajority 
for [B] so does [T] , while being able to ignore yet more equivocating votes 
from an equivocating voter.
>>
  
TODO: Really important
*)
Lemma blocks_with_super_majority_are_related 
  {voters:Voters}
  (T : Votes voters) 
  (is_safe_t: is_safe T = true)
  : forall (block1 block2:AnyBlock) (v1 v2:nat), 
    List.In (block1,v1) (get_supermajority_blocks T)
    -> List.In (block2,v2) (get_supermajority_blocks T)
    -> (projT2 block1) ~ (projT2 block2).
Proof.
  intros ab1 ab2 v1 v2 H1 H2.
  destruct ab1 as [n1 b1] eqn:Hab1.
  destruct ab2 as [n2 b2] eqn:Hab2.
  simpl.
  remember (get_supermajority_blocks  T) as gt eqn:Heq_gt.
  unfold get_supermajority_blocks in Heq_gt.
  remember (split_voters_by_equivocation T) as splitedT.
  destruct splitedT as [equivocated_voters non_equivocate_voters].
  rewrite Heq_gt in H1.
  rewrite (List.filter_In) in H1.
  destruct H1 as [count1 ineq1].
  rewrite Heq_gt in H2.
  rewrite (List.filter_In) in H2.
  destruct H2 as [count2 ineq2].
  (*rewrite PeanoNat.Nat.ltb_lt in ineq1.
  rewrite PeanoNat.Nat.ltb_lt in ineq2.
  pose (PeanoNat.Nat.add_lt_mono _ _ _ _ ineq1 ineq2) as ineq.
  *)

  Admitted.

Open Scope list.

Lemma list_in_location {A} (x:A) l : 
  List.In x l <-> exists l1 l2, l = l1 ++ x::l2.
Proof.
  split.
  - intro H.
    induction l.
    + simpl in H.
      contradiction.
    + simpl in H.
      destruct H as [eq_a_x|in_l].
      * exists nil.
        exists l.
        rewrite eq_a_x.
        reflexivity.
      * apply IHl in in_l.
        destruct in_l as [l1].
        destruct H as [l2].
        exists (a::l1).
        exists l2.
        simpl.
        rewrite H.
        reflexivity.
  - intro H. 
    destruct H as  [l1].
    destruct H as  [l2].
    rewrite H.
    apply List.in_elt.
Qed.


Lemma superset_has_subset_majority_blocks_aux1  l p (b:AnyBlock) : 
  (exists v:nat, List.In (b,v) l /\ p (b,v)= true )
  -> exists v:nat, List.In (b,v) (List.filter p l).
Proof.
  intro H.
  destruct H as [v].
  exists v.
  apply List.filter_In.
  auto.
Qed.

Definition VotesIsSubset  
  {voters:Voters }
  (S : Votes voters )
  (T : Votes voters) 
  :Prop
  :=
  forall (vote: Vote voters), 
    (count vote_eqb vote  (votes_to_list S)
    <= count vote_eqb vote (votes_to_list T))%nat.

Definition intersection  
  {voters:Voters }
  (S : Votes voters)
  (T : Votes voters)
  : Votes voters.
Admitted.

Definition difference  
  {voters:Voters}
  (S : Votes voters)
  (T : Votes voters)
  : Votes voters.
Admitted.

Lemma is_votes_subset_transitive  
  {voters:Voters}
  (S1 S2 S3 : Votes voters)
  (s1_s2 : VotesIsSubset S1 S2)
  (s2_s3 : VotesIsSubset S2 S3)
  : VotesIsSubset S1 S3.
Proof.
  unfold VotesIsSubset.
  intro vote. 
  pose (s1_s2 vote) as ineq1.
  pose (s2_s3 vote) as ineq2.
  transitivity (count vote_eqb vote (votes_to_list S2));auto.
Qed.


(* TODO:  Really important *)
Lemma superset_has_subset_majority_blocks 
  {voters:Voters}
  (S : Votes voters) 
  (T : Votes voters) 
  (safe_proof: is_safe T  =true)
  (is_subset: VotesIsSubset S T)
  : forall anyblock anyblock_votes, 
      List.In (anyblock,anyblock_votes) (get_supermajority_blocks  S)
      -> {anyblock_votes_in_t 
          & List.In (anyblock,anyblock_votes_in_t) (get_supermajority_blocks  T)}.
Proof.
  intros b b_votes_number HinS.
  unfold get_supermajority_blocks in HinS.
  remember (split_voters_by_equivocation S) as splited_votes_S.
  destruct splited_votes_S as [equivocate_voters_s non_equivocate_voters_s] eqn:Hsplited_votes_S.
  apply List.filter_In in HinS.

  unfold get_supermajority_blocks.
  remember (split_voters_by_equivocation T) as splited_votes_T.
  destruct splited_votes_T as [equivocate_voters_T non_equivocate_voters_T] eqn:Hsplited_votes_T.
  Admitted.
  (*
  apply superset_has_subset_majority_blocks_aux1.
  assert 
    ( has_supermajority_predicate voters (length equivocate_voters_T) (b, v) =
    true
    )

  rewrite List.filter_In.

  destruct HinS as  [l1 HinS].
  destruct HinS as  [l2 HinS].
  

Admitted.
   *)
  

Definition has_supermajority 
  {voters:Voters}
  (S : Votes voters)
  : bool
  := 
  0 <? length (get_supermajority_blocks  S) .

Close Scope blocks_scope.
