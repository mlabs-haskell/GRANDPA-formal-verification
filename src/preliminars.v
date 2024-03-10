
Require Coq.Vectors.Vector.

Require List.
Require Nat.
Require Coq.Init.Nat.

Definition Vector := VectorDef.t.




Module BlockChain.
(* 
  
*)

Inductive Block : nat -> Type:= 
  | OriginBlock : Block 0
  | NewBlock {n} (oldBlock : Block n) (id:nat) : Block (S n).



(* 
  In the paper they constantly use B < B' as blocks, using the fact
   that a block contains the hash of it's predecessor. To facilitate 
   our lives, we replaced the hash of the previous block with the 
   entire Block-Chain. This isn't wise in a real implementation,
   but would simplify our proofs.
   This means that whenever the paper compares two blocks we would 
   replace the statement with a equivalent one comparing two 
   Chains.
   Additionally we are choosing Vectors to represent a chain of blocks 
   since we are only interested in two things: 
   - Block number (provided by the index of the block in the chain)
   - A way to have different blocks.
 *)

(* 
  This corresponds to head(C) <= head(C').
  There exits various ways to define this relation but we believe 
  that this one would be quite useful.
*)
Inductive Prefix : forall {n}, Block n -> forall {m}, Block m -> Type :=
  (* C <= C*)
  | Same : forall n (block : Block n), Prefix block block
  (* C <= C'  ->  C <= (B :: C')*)
  | IsPrefix {n m} (block1: Block n) (block2: Block m) (block_id : nat) :
      Prefix block1 block2 -> Prefix block1 (NewBlock block2 block_id).


(* 
   Is equivalent to the relation B ~ B' in the paper
   We express it like `(B <= B' ) /\ (B' <= B)` instead 
   of the one in the paper `B<B' /\ B=B! /\ B>B'` .

 *)
Variant Related : forall {n}, Block n -> forall {m}, Block m -> Prop :=
  | IsLower {n m } (block1:Block n) (block2:Block m) 
    : Prefix block1 block2 -> Related block1 block2
  | IsUpper {n m } (block1:Block n) (block2:Block m)  
    : Prefix block2 block1 -> Related block2 block1.

Definition Unrelated {n m} (block1 : Block n) (block2 :Block m) : Type := not (Related block1 block2).


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


Definition has_supermajority  {bizantiners_number last_block_number}
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


(* Función g *)
Definition g {bizantiners_number last_block_number out}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T : Votes voters last_block) 
  : option (Block out).
(* TODO: Provide definition *)
Admitted.

(*
  let valid_votes := 
    filter (fun v => match v with 
                     | VoteC _ _ _ _ _ _ => true 
                     | _ => false 
                     end) 
           (projT2 T) in
  let sorted_votes := 
    sort (fun v1 v2 => if leb (projT2 v1) (projT2 v2) then true else false) 
         valid_votes in
  match sorted_votes with
  | [] => OriginBlock
  | h :: _ => projT1 h
  end.
*)

Definition IsSubset {bizantiners_number last_block_number_s last_block_number_t} 
  {voters:Voters bizantiners_number}
  {last_block_s : Block last_block_number_s}
  {last_block_t : Block last_block_number_t}
  (S : Votes voters last_block_s)
  (T : Votes voters last_block_t) : Prop.
Admitted.

Lemma lemma_2_5_2 {bizantiners_number last_block_number}
  {voters:Voters bizantiners_number}
  {last_block : Block last_block_number}
  (T: Votes voters last_block)
  (is_safe_t: isSafe T = true)
  (S: Votes voters last_block) 
  (is_sub_set: IsSubset S T )
  {gs_block_number: nat}
  (gs : Block gs_block_number)
  (gs_is_result : g S = Some gs)
  (gt_block_number: nat)
  (gt : Block gt_block_number)
  (gt_is_result : g T = Some gt)
  :Prefix gs gt. 
Admitted.


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
  (gs_is_result : g S = Some gs)
  {block_number : nat}
  (block: Block block_number)
  (unrelated_proof: Unrelated block gs)
  : ImpossibleSupermajority S block.
Admitted.

  



(* TODO: Define:

- Time
- Round
- Estimate 

Module preliminars.


Inductive Maybe : Type -> Type :=
 | Just  {T:Type}  (t:T) : Maybe T
 | Nothing  {T:Type}: Maybe T.

Definition SetOfVotes := nat.

Definition checkSuperMajority (S:SetOfVotes) : bool := true.



Definition g (n:SetOfVotes) : Maybe Block := Nothing.



Example SOme : Block = Block .


Inductive Time := | TimeC nat.

Definition Voter := nat.

Definition Voters := list nat.

Definition Vote := list Block.

Inductive Round : Voters-> Time -> nat -> Type := 
  | EmptyRound  (vs:Voters) (t:Time) (round_number:nat) : 
      Round vs t round_number
  | RoundStep {vs:Voters} {t_prev:Time} {round_number:nat}  
    (previous_step:Round vs t_prev round_number)  
    (new_votes:list (Vote * nat) ): 
    Round vs (t_prev +1) round_number
  | NewRound {vs:Voters} {t_prev:Time} {round_number:nat}  
    (previous_round:Round vs t_prev round_number)  
    (new_voters:Voters ): 
    Round new_voters (t_prev +1) (round_number+1).




 *)
End BlockChain.

