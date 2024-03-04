
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
  | Same : forall n (B : Block n), Prefix B B
  (* C <= C'  ->  C <= (B :: C')*)
  | IsPrefix {n m} (B: Block n) (B': Block m) (b : nat) :
      Prefix B B' -> Prefix B (NewBlock B b).


(* 
   Is equivalent to the relation B ~ B' in the paper
   We express it like `(B <= B' ) /\ (B' <= B)` instead 
   of the one in the paper `B<B' /\ B=B! /\ B>B'` .

 *)
Inductive Related : forall {n}, Block n -> forall {m}, Block m -> Type :=
  | IsLower {n m } (B:Block n) (B':Block m) : Prefix B B' -> Related B B'
  | IsUpper {n m } (B:Block n) (B':Block m)  : Prefix B' B -> Related B' B.


Inductive Voter : Type := |VoterC (n:nat) :Voter.

Inductive Vote {n} : Block n -> Type := 
  | VoteC {m} {original_chain: Block n} (block: Block m) (is_prefix: Prefix original_chain block) (voter : Voter) : Vote original_chain.

Inductive Votes {n} : Block n ->  Type := | VotesC (B : Block n) (l:list (Vote B)): Votes B.



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
End preliminars.

