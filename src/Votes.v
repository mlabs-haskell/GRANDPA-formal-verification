Require List.
Require Import  Nat.
Require Import Blocks.

Require Dictionary.

Definition Voter : Type := nat.

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


Definition votes_to_pair_list {bizantiners_number last_block_number}
  {voters: Voters bizantiners_number} {last_block:Block last_block_number}
  (votes: Votes voters last_block)
  : list (nat * (sigT (fun n => Block n)))
  :=
  match votes with 
    | VotesC _ _ list => 
        List.map vote_to_pair list
  end.

Definition is_equivocate {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (voter: Voter)
  (votes: Votes voters last_block)
  : bool
  :=
    let unvote vote1 := match  vote1 with
      |VoteC  _ _  voter _ _ _ => voter
      end
    in
    match votes with 
    | VotesC  _ _ votes_list => 
      let voters_list : list Voter := List.map unvote votes_list
      in
      let has_same_voter (new_vote : Voter) := Nat.eqb new_vote voter 
      in
      let filtered := List.filter has_same_voter voters_list
      in
        Nat.ltb (length filtered) 1
    end.

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
     length equivocate_voters <? bizantiners_number
  end.



Module BlockDictionaryTypes <: Dictionary.Types.
  Definition K := AnyBlock.
  Definition V := nat.
  Definition eqb := any_block_eqb.
End BlockDictionaryTypes.

Module BlockDictionaryModule := Dictionary.Functions BlockDictionaryTypes.

Definition BlockDictionary := BlockDictionaryModule.Dictionary AnyBlock nat.

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



Definition count_vote {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (vote :Vote voters last_block) (acc: BlockDictionary): BlockDictionary
  :=
  match vote with
  | VoteC _ _ _ _ block prefix_proof => count_vote_aux block prefix_proof acc
  end.

Fixpoint count_votes_aux {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes:list (Vote voters last_block)) (acc: BlockDictionary): (list (Vote voters last_block)) * BlockDictionary
  :=
  match votes with
  | List.nil => (List.nil, acc)
  | List.cons vote remain => count_votes_aux remain (count_vote vote acc)
  end.

Definition count_votes {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block): BlockDictionary
  :=
  match count_votes_aux (votes_to_list votes) BlockDictionaryModule.empty with
  | (_ , out) => out
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

Definition has_supermajority  {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S : Votes voters last_block) 
  : bool.
Admitted.

(*
  let n := length voters in
  let threshold := (n + f + 1) / 2 in
  let valid_votes := 
    filter (fun v => match v with 
                     | VoteC _ _ _ _ _ _ => true 
                     end) 
           voters in
  let valid_votes_count := length valid_votes in
  let equivocating_voters := 
    voters_upper - length (remove_duplicates Nat.eq_dec 
                                (map (fun v => projT2 v) valid_votes)) in
  valid_votes_count >= threshold \/ equivocating_voters >= f.
*)

Definition IsSubset {bizantiners_number last_block_number_s last_block_number_t} 
  {voters:Voters bizantiners_number}
  {last_block_s : Block last_block_number_s}
  {last_block_t : Block last_block_number_t}
  (S : Votes voters last_block_s)
  (T : Votes voters last_block_t) : Prop.
Admitted.


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
