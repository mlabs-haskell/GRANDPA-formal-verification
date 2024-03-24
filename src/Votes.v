Require List.
Require Import  Nat.
Require Import Blocks.

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
