
Require Coq.Vectors.Vector.

Require List.

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
Inductive Related : forall {n}, Block n -> forall {m}, Block m -> Type :=
  | IsLower {n m } (block1:Block n) (block2:Block m) 
    : Prefix block1 block2 -> Related block1 block2
  | IsUpper {n m } (block1:Block n) (block2:Block m)  
    : Prefix block2 block1 -> Related block2 block1.


Definition Voter : Type := nat.

Definition Voters: Type := list Voter.

Inductive Vote {last_block_number} 
  :Voters -> Block last_block_number -> Type 
  := 
    | VoteC {m}  (voters : Voters) (voter : Voter) 
      (is_voter: List.In voter voters ) 
      (original_chain: Block last_block_number) 
      (block: Block m) (is_prefix: Prefix original_chain block)
      : Vote voters original_chain.


Inductive Votes  {last_block_number}
  : Voters -> Block last_block_number ->  Type 
  := 
    | VotesC (voters:Voters ) {B : Block last_block_number}
      (votes_list:list (Vote voters B))
      : Votes voters B.


Definition has_supermajority  {last_block_number}
  (voters:Voters)
  (last_block : Block last_block_number)
  (S : Votes voters last_block) 
  (f : nat) 
  (f_is_low : (3 * f < length voters))
  : Type.
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

Inductive Maybe : Type -> Type :=
 | Just  {T:Type}  (t:T) : Maybe T
 | Nothing  {T:Type}: Maybe T.

(* Función g *)
Definition g {last_block_number} 
  (voters:Voters)
  (last_block : Block last_block_number)
  (T : Votes voters last_block) 
  : Maybe (Block last_block_number).
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

(* TODO: Define:

- Time
- Voter 
- Set of Votes 
- SuperMajority
- g
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

