Require List.
Require Import Grandpa.Blocks.

Definition Voter : Type := nat.

Variant Voters (bizantiners_number:nat) : Type 
  := 
    | VotersC (voters:list Voter) 
        (*TODO: add a constraint here to make the voters to only appear 
        once, or use a proper set.*)
        (bizantiners_are_lower: 3*bizantiners_number < length voters) 
      : Voters  bizantiners_number .


Definition inVoters {bizantiners_number} 
  (voter : Voter) (voters:Voters bizantiners_number) 
  :=
  match voters with 
  | VotersC _ l _ => List.In voter l
  end.

Definition votersLength {bizantiners_number} (voters:Voters bizantiners_number)
  := 
  match voters with
  | VotersC _ l _ => length l
  end.

Inductive Vote {bizantiners_number last_block_number}
  :Voters bizantiners_number -> Block last_block_number -> Type 
  := 
    | VoteC {m}  (voters : Voters bizantiners_number) (voter : Voter) 
      (is_voter: inVoters voter voters ) 
      (original_chain: Block last_block_number) 
      (block: Block m) (is_prefix: Prefix original_chain block)
      : Vote voters original_chain.


Inductive Votes  {bizantiners_number last_block_number}
  (voters: Voters bizantiners_number) (last_block:Block last_block_number)
  :Type 
  := 
    | VotesC
      (votes_list:list (Vote voters last_block))
      : Votes voters last_block.


Definition Equivocate {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (voter: Voter)
  (votes: Votes voters last_block)
  : bool
  :=
    let unvote vote1 := match  vote1 with
      |VoteC  _  voter _ _ _ _ => voter
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

Fixpoint isSafe {bizantiners_number last_block_number } 
  {voters: Voters bizantiners_number}
  {last_block : Block last_block_number}
  (votes: Votes voters last_block)
  :bool.
  Admitted.
  (*
    match voters with 
    | VotersC  _ voters_list _ => 
        match voters_list with
        | nil => true
        | List.cons x y => andb (negb (Equivocate x votes) ) (isSafe (Votes voters y))
        end
     end.
  *)


Definition hasSupermajority  {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (S : Votes voters last_block) 
  : bool.
(* TODO: Provide Definition *)
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
