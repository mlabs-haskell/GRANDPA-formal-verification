Require List.
Require Import  Nat.
Require Import Coq.Program.Equality.
Require Coq.Program.Wf.

Require Dictionary.
Require Import Blocks.
Require Import ListFacts.

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

Variant Unit := | UnitC.

Variant Voters (bizantiners_number:nat) : Type 
  := 
    | VotersC (voters: Dictionary.Dictionary Voter Unit) 
      : Voters  bizantiners_number .

Definition voters_to_list {bizantiners_number} (voters:Voters bizantiners_number)
  := 
  match voters with
  | VotersC _ d => List.map fst (Dictionary.to_list d)
  end.

Definition voters_length {bizantiners_number} (voters:Voters bizantiners_number)
  := 
  length (voters_to_list voters).

Definition voters_from_list (bizantiners_number:nat) (voters:list Voter)
  : Voters bizantiners_number
  :=
  VotersC bizantiners_number 
    (Dictionary.from_list Nat.eqb (List.map (fun n => (n,UnitC)) voters)).


Definition voters_eqb {bizantiners_number} 
  (v1 v2:Voters bizantiners_number)
  : bool
  := list_beq nat Nat.eqb (voters_to_list v1) (voters_to_list v2).

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
      (block: Block m) (is_prefix: original_chain <= block)
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

Definition vote_to_block  {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number}
  {original_chain:Block last_block_number}
  (vote: Vote voters original_chain)
  : (sigT (fun n => Block n))
  :=
  match vote with 
  | VoteC _ _ voter _ block _ => 
        existT _ _ block
  end.

Definition vote_eqb {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number}
  {original_chain:Block last_block_number}
  (vote1 vote2: Vote voters original_chain)
  : bool
  :=
  match vote1,vote2 with
  | VoteC _ _ voter1' _ block1 _ , VoteC _ _ voter2' _ block2 _
      =>
      (voter1' =? voter2')%nat && (block1 =? block2)
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
  0 <? count Nat.eqb voter (votes_to_voters_list votes).

Definition is_equivocate {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (voter: Voter)
  (votes: Votes voters last_block)
  : bool
  := 1 <? count Nat.eqb voter ( votes_to_voters_list votes).

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
  match List.find (fun m => (n =? m)%nat) l with
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

Definition BlockDictionary := Dictionary.Dictionary AnyBlock nat.

(** ** Vote count

- First we split the set of votes in two, one of votes 
  made by equivocate voters and other made by 
   non equivocate voters
- We count the total votes for all the block that 
  were votes (that is, we don't count the 
   blocks b such that   b < b'  and last_block < b
   when some voter voted for b' but not for b)
- Then we do a "flatten" it means for every 
  voted block b, if b' < b and last_block < b
   then we add the votes for b to the votes for b'.
*)


(**
  This function takes a block and a list of blocks 
   and counts all the times the block appears in it.
 *)
Definition count_block_votes
  (block: AnyBlock) 
  (votes_as_list : list AnyBlock)
  (acc: BlockDictionary): BlockDictionary
  :=
    let number_of_votes_for_block 
      := count Blocks.anyblock_eqb block votes_as_list
    in
      Dictionary.add Blocks.anyblock_eqb block number_of_votes_for_block acc.


Lemma count_block_votes_permutation 
  (block: AnyBlock) 
  :forall l1 l2 b1 b2 (acc: BlockDictionary),
    count_block_votes block (l1++b1::b2::l2) acc
    =count_block_votes block (l1++b2::b1::l2) acc.
Proof.
  intros.
  simpl.
  unfold count_block_votes.
  rewrite count_permutation.
  reflexivity.
Qed.

(**
Previously we used another version using List.filter
but then we were require to proof that (length votes)
decreases and that makes the resultant function unmanageable.

[Definition aux2
  (block:AnyBlock) (remain_blocks:list AnyBlock)
  := List.filter 
      (fun b => negb (Blocks.anyblock_eqb block b)) remain_blocks.
]
*)
Fixpoint make_votes_dictionary_aux
  (votes:list AnyBlock) (previous:list AnyBlock) (acc: BlockDictionary)
  :(list AnyBlock) * BlockDictionary
  :=
  match votes with
  | List.nil => (List.nil, acc)
  | List.cons block remain_blocks => 
    if (count anyblock_eqb block previous =? 0)%nat
    then
      let updated_dict := 
        count_block_votes block votes acc
      in
      make_votes_dictionary_aux
        remain_blocks
        (block :: previous)
        updated_dict
    else
      make_votes_dictionary_aux
        remain_blocks
        (block :: previous)
        acc
  end.

Lemma make_votes_dictionary_aux_step_cons_cons_destruct
  (b1 b2:AnyBlock)
  (votes:list AnyBlock) 
  :forall (acc: BlockDictionary) l1 l2, anyblock_eqb b1 b2=true
  -> make_votes_dictionary_aux votes (l1 ++ b1::b2::l2) acc
    =  make_votes_dictionary_aux votes (l1++b2::l2) acc.
Proof.
  induction votes.
  - reflexivity.
  - intros acc l1 l2 b1_eq_b2. 
    simpl.
    rewrite count_concat.
    rewrite count_concat.
    rewrite count_cons.
    rewrite count_cons.
    destruct (anyblock_eqb a b2) eqn:a_b2.
    + simpl.
      Search (?m + S ?n = S (?m + ?n) ).
      rewrite PeanoNat.Nat.add_succ_r.
      rewrite PeanoNat.Nat.add_succ_r.
      rewrite PeanoNat.Nat.add_succ_r.
      simpl.
      apply (IHvotes acc (a::l1)%list l2).
      auto.
    + simpl.
      assert (anyblock_eqb a b1 = false).
        {
          destruct (anyblock_eqb a b1) eqn:Hab2.
          - pose (anyblock_eqb_transitive a b1 b2 Hab2 b1_eq_b2) as contra.
            rewrite contra in a_b2.
            auto.
          - auto.
        }
      rewrite H.
      simpl.
      destruct (count anyblock_eqb a l1 + count anyblock_eqb a l2 =? 0)%nat;
      apply (IHvotes _ (a::l1)%list l2 );auto.
Qed.

Lemma make_votes_dictionary_aux_commutative
  (b1:AnyBlock)
  : 
    forall  l1 l3 (acc: BlockDictionary) b2
    ,make_votes_dictionary_aux (l1++b1::b2 :: nil) l3 acc
    = make_votes_dictionary_aux (l1++b2::b1::nil) l3 acc.
Proof.
  induction l1.
  - simpl.
    intros.
    destruct (count anyblock_eqb b1 l3 =? 0)%nat eqn:H1
    ;destruct (count anyblock_eqb b2 (b1 :: l3) =? 0)%nat eqn:H2   
    ;destruct (count anyblock_eqb b2 l3 =? 0)%nat eqn:H3
    ;destruct (count anyblock_eqb b1 (b2 :: l3) =? 0)%nat eqn:H4.
    (*    2:{ simpl.
    + unfold make_votes_dictionary_aux.
      

  - simpl.
    intros.
    destruct (count anyblock_eqb a l3 =? 0)%nat.
    + simpl.
    rewrite (IHl1 l2 (a::l3)%list _).
    rewrite (count_block_votes_permutation a (a::l1) l2 b1 b2  ).
    reflexivity.
    *)
    Admitted.



Print count_after_filter_is_zero.
Lemma make_votes_dictionary_aux_step 
  (block:AnyBlock)
  (votes:list AnyBlock) 
  : forall (acc: BlockDictionary),
  make_votes_dictionary_aux (block :: votes) nil acc
    = make_votes_dictionary_aux 
        (List.filter (fun block2 =>negb ( anyblock_eqb block block2 )) votes)  
        nil
        (count_block_votes block (block ::votes ) acc).
Proof.
  induction votes.
  - intros *. reflexivity.
  - destruct (anyblock_eqb block a) eqn:block_eq_a.
    + simpl.
      unfold count.
      simpl.
      rewrite block_eq_a.
      apply anyblock_eqb_symmetric in block_eq_a.
      rewrite block_eq_a.
      simpl.
      intro acc.
      rewrite (make_votes_dictionary_aux_step_cons_cons_destruct a block votes _ nil nil block_eq_a).
      simpl.
      simpl in IHvotes.
      unfold count_block_votes.

      unfold make_votes_dictionary_aux in IHvotes.



(*
  This function takes the list of votes (befor flatten)
   and counts the number of votes for every vote
*)

Definition make_votes_dictionary
  (votes:list AnyBlock)  (acc: BlockDictionary)
  : BlockDictionary
  := snd (make_votes_dictionary_aux votes List.nil acc).


Lemma make_votes_dictionary_votes_end_empty_aux 
   (votes:list AnyBlock)
    : forall (acc: BlockDictionary) l, fst (make_votes_dictionary_aux votes l acc) = nil.
Proof.
  induction votes.
  - auto.
  - simpl.
    intros acc l.
    destruct (count anyblock_eqb a l =? 0)%nat.
    + apply IHvotes.
    + apply IHvotes.
Qed.


(**
  A vote for [B: Block n] is also a vote for [B':Block n'] 
   as long as [B' <= B] and last_block <= B'. 
*)
Fixpoint flat_votes_aux {m}
  (last_block_number:nat) 
  (block:Block m)
  (voter_number:nat)
  (acc: BlockDictionary): BlockDictionary
  :=
  if last_block_number <? m 
  then 
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
        flat_votes_aux last_block_number older_block voter_number updated_acc
    end
  else
    acc.

Definition flat_votes_dictionary 
  (last_block_number:nat) 
  (acc:BlockDictionary) : BlockDictionary
  := 
  List.fold_right 
    (
      fun anyblock updated_dict 
      =>
      match anyblock with
      | (block,votes_for_block)
          => flat_votes_aux 
            last_block_number (projT2 block) votes_for_block updated_dict
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
Definition count_votes {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block): BlockDictionary
  :=
  match make_votes_dictionary (List.map vote_to_block (votes_to_list votes)) Dictionary.empty with
  | out => flat_votes_dictionary last_block_number out
  end.

Lemma count_votes_nil_is_zero {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block)
  : votes_to_list votes = nil 
    -> Dictionary.to_list (count_votes votes) = nil.
Proof.
  intro H.
  unfold count_votes.
  rewrite H.
  reflexivity.
Qed.

Lemma count_votes_works {bizantiners_number last_block_number}
  {block_number:nat}
  (block: Block block_number)
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  :forall (votes: list (Vote  voters last_block))
  (v:nat)
  , 
   List.In 
     (existT _ block_number block,v) 
     (Dictionary.to_list (count_votes (VotesC voters last_block votes)))
     ->
     v = length (
       List.filter (
         fun vote => is_prefix block (projT2 (vote_to_block vote))
       ) 
       (votes_to_list (VotesC voters last_block votes)) 
      ).
Proof.
  induction votes as [|vote remain_votes] eqn:eq_votes_list.
  - intros v Hv. 
    inversion Hv.
  - intros v Hv.
    simpl.
    unfold count_votes in Hv.
    simpl in Hv.
    unfold make_votes_dictionary in Hv.
    unfold make_votes_dictionary_aux in Hv.
    simpl in Hv.
    destruct (is_prefix block (projT2 (vote_to_block vote)))  eqn:Hprefix.
    + simpl.




Lemma voted_block_in_count_votes {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block)
  {voter:Voter }
  {is_voter: in_Voters voter voters}
  {block_number:nat}
  {block: Block block_number}
  {is_prefix_proof: last_block <= block}
  (vote: Vote voters last_block)
  {vote_is: vote = VoteC voters last_block voter is_voter block is_prefix_proof}
  (is_vote : List.In vote (votes_to_list votes))
  : exists v:nat
    , List.In 
      (existT _ block_number block,v) 
      (Dictionary.to_list (count_votes votes)).
Proof.
  exists (count_block_votes )
  Search List.In.
  unfold count_votes.
  Search (List.map).
  apply (List.in_map vote_to_block) in is_vote as block_in_votes.
  unfold make_votes_dictionary.
  unfold make_votes_dictionary_aux.
  simpl.
  simpl. 

  Admitted.


Module Example1.

Example e_block1 := NewBlock OriginBlock 10.
Example e_block2 := NewBlock OriginBlock 11.
Example e_block3 := NewBlock OriginBlock 12.
Example e_block4 := NewBlock OriginBlock 10.
Example e_block5 := NewBlock OriginBlock 10.
Example e_block6 := NewBlock OriginBlock 10.
Example e_block7 := NewBlock (NewBlock OriginBlock 10) 22.
Example e_block8 := NewBlock (NewBlock OriginBlock 11) 22.
Example e_block9 := NewBlock (NewBlock OriginBlock 10) 23.

Open Scope list.
Example e_voters_list := (1::2::3::4::5::6::7::8::9::List.nil).

Example e_voters := voters_from_list 1 e_voters_list. 

Example false_in x : in_Voters x e_voters.
Admitted.

Definition mk {m} n (b: Block m) := 
  VoteC e_voters OriginBlock n (false_in n) b (originBlock_is_always_prefix b).

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

Example e_votes := VotesC e_voters OriginBlock votes_list.

(**
[Compute count_votes e_votes.
= Dictionary.DictionaryC AnyBlock nat
         ((existT (fun n : nat => Block n) 2
             (NewBlock (NewBlock OriginBlock 10) 23), 1)
          :: (existT (fun n : nat => Block n) 1 (NewBlock OriginBlock 10), 6)
             :: (existT (fun n : nat => Block n) 2
                   (NewBlock (NewBlock OriginBlock 11) 22), 1)
                :: (existT (fun n : nat => Block n) 1
                      (NewBlock OriginBlock 11), 2)
                   :: (existT (fun n : nat => Block n) 2
                         (NewBlock (NewBlock OriginBlock 10) 22), 1)
                      :: (existT (fun n : nat => Block n) 1
                            (NewBlock OriginBlock 12), 1) :: nil)
     : BlockDictionary
]
*)

Close Scope list.

End Example1.

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

Definition has_supermajority_predicate {bizantiners_number}
  (voters:Voters bizantiners_number)
  (number_of_equivocates:nat)
  (block_and_vote:AnyBlock*nat) : bool:= 
    match block_and_vote with
    | (_, number_of_votes) 
        => 
        voters_length voters + bizantiners_number +1 
        <? 2 * (number_of_votes + number_of_equivocates)
    end.



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
        (voters_from_list bizantiners_number non_equivocate_voters)
      )
  in
  let blocks_with_super_majority 
    := 
    List.filter 
      (has_supermajority_predicate voters number_of_equivocates)
      (Dictionary.to_list count)
  in
    blocks_with_super_majority.

(*
Compute split_voters_by_equivocation Example1.e_votes .
Compute count_votes Example1.e_votes.
Compute voters_length Example1.e_voters.

Compute get_supermajority_blocks Example1.e_votes .


Example e1 : 
  get_supermajority_blocks Example1.e_votes 
    = List.cons (existT (fun n : nat => Block n) 1 (NewBlock OriginBlock 10), 6) List.nil.
Proof.
  reflexivity.
  unfold get_supermajority_blocks.
  simpl.

*)

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
    (count vote_eqb vote  (votes_to_list S)
    <= count vote_eqb vote (votes_to_list T))%nat.

Lemma aux {A} (l l1 l2:list A) p 
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
(*Lemma superset_has_equivocates_of_subset {bizantiners_number last_block_number}
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
  Search List.filter.
  Admitted.
 *)

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
  (* TODO: add is_safe hip *)
  (T : Votes voters last_block) 
  : forall (block1 block2:AnyBlock) (v1 v2:nat), 
    List.In (block1,v1) (get_supermajority_blocks T)
    -> List.In (block2,v2) (get_supermajority_blocks T)
    -> (projT2 block1) ~ (projT2 block2).
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
  (*rewrite PeanoNat.Nat.ltb_lt in ineq1.
  rewrite PeanoNat.Nat.ltb_lt in ineq2.
  pose (PeanoNat.Nat.add_lt_mono _ _ _ _ ineq1 ineq2) as ineq.
  *)
  (* Search (?n * ?m < ?n * ?w). *)

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
  intros b b_votes_number HinS.
  unfold get_supermajority_blocks in HinS.
  remember (split_voters_by_equivocation S) as splited_votes_S.
  destruct splited_votes_S as [equivocate_voters_s non_equivocate_voters_s] eqn:Hsplited_votes_S.
  apply List.filter_In in HinS.

  unfold get_supermajority_blocks.
  remember (split_voters_by_equivocation T) as splited_votes_T.
  destruct splited_votes_T as [equivocate_voters_T non_equivocate_voters_T] eqn:Hsplited_votes_T.
  apply superset_has_subset_majority_blocks_aux1.

  assert 
    ( has_supermajority_predicate voters (length equivocate_voters_T) (b, v) =
    true
    )

  rewrite List.filter_In.

  destruct HinS as  [l1 HinS].
  destruct HinS as  [l2 HinS].
  
  Search (List.In ?x ?l -> ?l1 ++ (?x :: ?l2) = ?l).
  Search (List.find).
  Print List.find.

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

Close Scope blocks_scope.
