
Module preliminars.


Inductive Maybe : Type -> Type :=
 | Just  {T:Type}  (t:T) : Maybe T
 | Nothing  {T:Type}: Maybe T.

Definition SetOfVotes := nat.

Definition checkSuperMajority (S:SetOfVotes) : bool := true.

Definition Block := nat.

Definition g (n:SetOfVotes) : Maybe Block := Nothing.




Definition Time := nat.

Definition Voter := nat.

Definition Voters := list nat.

Definition Vote := list Block.

Inductive Round : Voters-> Time -> nat -> Type := 
  | EmptyRound  (vs:Voters) (t:Time)  (round_number:nat) : Round vs t round_number
  | NextRound {vs:Voters} {t_prev:Time} {r:nat}  (previous_round:Round vs t_prev r)  (new_votes:list (Vote * nat) ) : Round vs (t_prev +1) r.




End preliminars.
